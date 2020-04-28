library('rlang')
library('stringr')
library('EpiModel')
library('deSolve')
library('data.table')
library('adaptivetau')
library('qs')
library('RcppGSL')
library('socialmixr')
library('reshape2')
library('ggplot2')


data("polymod")
x1<-contact_matrix(polymod, countries = "United Kingdom" , age.limits =c(0, 5, 18, 30, 40, 50, 60, 70), symmetric = TRUE)
x2<-(x1$matrix+t(x1$matrix))/2

set.seed(22042020)

q<- 0.54

b_00 <- x2[1,1]*q
b_05 <- x2[1,2]*q
b_018<- x2[1,3]*q
b_030<- x2[1,4]*q
b_040<- x2[1,5]*q
b_050<- x2[1,6]*q
b_060<- x2[1,7]*q
b_070<- x2[1,8]*q
b_55<-  x2[2,2]*q
b_518<- x2[2,3]*q
b_530<- x2[2,4]*q
b_540<- x2[2,5]*q
b_550<- x2[2,6]*q
b_560<- x2[2,7]*q
b_570<- x2[2,8]*q
b_1818<-x2[3,3]*q
b_1830<-x2[3,4]*q
b_1840<-x2[3,5]*q
b_1850<-x2[3,6]*q
b_1860<-x2[3,7]*q
b_1870<-x2[3,8]*q
b_3030<-x2[4,4]*q
b_3040<-x2[4,5]*q
b_3050<-x2[4,6]*q
b_3060<-x2[4,7]*q
b_3070<-x2[4,8]*q
b_4040<-x2[5,5]*q
b_4050<-x2[5,6]*q
b_4060<-x2[5,7]*q
b_4070<-x2[5,8]*q
b_5050<-x2[6,6]*q
b_5060<-x2[6,7]*q
b_5070<-x2[6,8]*q
b_6060<-x2[7,7]*q
b_6070<-x2[7,8]*q
b_7070<-x2[8,8]*q


#PARAMETERS TAKEN SHAMELESSLY FROM CMMID MODEL RELEASED ON GITHUB IN THE BEGINNING OF APRIL

sigma <- 1/6.5  #1/serial interval
presmp <- 1/1.5   #1/average time from infectiousness to symptom onset
asymp <- 1/5 #1/average time of recovery from infectious to recov if asymptomatic

cc <- 1/8     #1/average time in critical care and in hospital (split 16 days to 8 and 8)
mort <- 0.5           #mortality proportion
p_symp <-0.66         #proportion who develop symptoms
p_hosp <-c(0,
           0.007615301,
           0.008086654,
           0.009901895,
           0.018535807,
           0.054306954,
           0.150514645,
           0.316848531)  #proportion of symptomatics who go to hospital
p_icu <-p_hosp*0.3  #proportion of those defined as symptomatic cases who go to hospital which will require ICU intervention


#assume contact is symmetrical
#assume that age of population is static
#assume all population is susceptible at start of epidemic

first.model <- function (t, x, ...) {
  s <- x[c("S0","S5","S18","S30", "S40", "S50", "S60", "S70")] # susceptibles #
  e <- x[c("E0","E5","E18","E30", "E40", "E50", "E60", "E70")] # pre-infectious
  ip <- x[c("IP0","IP5","IP18","IP30", "IP40", "IP50", "IP60", "IP70")] # infectious pre-symptomatic
  ia <- x[c("IA0","IA5","IA18","IA30", "IA40", "IA50", "IA60", "IA70")] # infectious asymptomatic
  is <- x[c("IS0","IS5","IS18","IS30", "IS40", "IS50", "IS60", "IS70")] #infectious sympyomatic
  h <- x[c("H0","H5","H18","H30", "H40", "H50", "H60", "H70")] # infected in hospital
  c <- x[c("C0","C5","C18","C30", "C40", "C50", "C60", "C70")] # critical care infected
  r <- x[c("R0","R5","R18","R30", "R40", "R50", "R60", "R70")] # recovered
  d <- x[c("D0","D5","D18","D30", "D40", "D50", "D60", "D70")] # dead rip
  n <- s+e+ip+ia+is+h+c+r+d # total pop
  lambda_0 <- b_00*(ip[1]+is[1]+ia[1])+b_05*(ip[2]+is[2]+ia[2])+b_018*(ip[3]+is[3]+ia[3])+b_030*(ip[4]+is[4]+ia[4])+b_040*(ip[5]+is[5]+ia[5])+b_050*(ip[6]+is[6]+ia[6])+b_060*(ip[7]+is[7]+ia[7])+b_070*(ip[8]+is[8]+ia[8]) # 0-5 FOI
  lambda_5 <- b_05*(ip[1]+is[1]+ia[1])+b_55*(ip[2]+is[2]+ia[2])+b_518*(ip[3]+is[3]+ia[3])+b_530*(ip[4]+is[4]+ia[4])+b_540*(ip[5]+is[5]+ia[5])+b_550*(ip[6]+is[6]+ia[6])+b_560*(ip[7]+is[7]+ia[7])+b_570*(ip[8]+is[8]+ia[8]) # 5-18 force of infection
  lambda_18 <- b_018*(ip[1]+is[1]+ia[1])+b_518*(ip[2]+is[2]+ia[2])+b_1818*(ip[3]+is[3]+ia[3])+b_1830*(ip[4]+is[4]+ia[4])+b_1840*(ip[5]+is[5]+ia[5])+b_1850*(ip[6]+is[6]+ia[6])+b_1860*(ip[7]+is[7]+ia[7])+b_1870*(ip[8]+is[8]+ia[8]) #18-30 foi
  lambda_30 <- b_030*(ip[1]+is[1]+ia[1])+b_530*(ip[2]+is[2]+ia[2])+b_1830*(ip[3]+is[3]+ia[3])+b_3030*(ip[4]+is[4]+ia[4])+b_3040*(ip[5]+is[5]+ia[5])+b_3050*(ip[6]+is[6]+ia[6])+b_3060*(ip[7]+is[7]+ia[7])+b_3070*(ip[8]+is[8]+ia[8]) #30-40
  lambda_40 <- b_040*(ip[1]+is[1]+ia[1])+b_540*(ip[2]+is[2]+ia[2])+b_1840*(ip[3]+is[3]+ia[3])+b_3040*(ip[4]+is[4]+ia[4])+b_4040*(ip[5]+is[5]+ia[5])+b_4050*(ip[6]+is[6]+ia[6])+b_4060*(ip[7]+is[7]+ia[7])+b_4070*(ip[8]+is[8]+ia[8]) #40-50
  lambda_50 <- b_050*(ip[1]+is[1]+ia[1])+b_550*(ip[2]+is[2]+ia[2])+b_1850*(ip[3]+is[3]+ia[3])+b_3050*(ip[4]+is[4]+ia[4])+b_4050*(ip[5]+is[5]+ia[5])+b_5050*(ip[6]+is[6]+ia[6])+b_5060*(ip[7]+is[7]+ia[7])+b_5070*(ip[8]+is[8]+ia[8]) #50-60
  lambda_60 <- b_060*(ip[1]+is[1]+ia[1])+b_560*(ip[2]+is[2]+ia[2])+b_1860*(ip[3]+is[3]+ia[3])+b_3060*(ip[4]+is[4]+ia[4])+b_1840*(ip[5]+is[5]+ia[5])+b_5060*(ip[6]+is[6]+ia[6])+b_6060*(ip[7]+is[7]+ia[7])+b_6070*(ip[8]+is[8]+ia[8]) #60-70
  lambda_70 <- b_070*(ip[1]+is[1]+ia[1])+b_570*(ip[2]+is[2]+ia[2])+b_1870*(ip[3]+is[3]+ia[3])+b_3070*(ip[4]+is[4]+ia[4])+b_4070*(ip[5]+is[5]+ia[5])+b_5070*(ip[6]+is[6]+ia[6])+b_6070*(ip[7]+is[7]+ia[7])+b_7070*(ip[8]+is[8]+ia[8]) #70+
  list(
    c(
      -lambda_0*s[1], #S-->E
      -lambda_5*s[2],
      -lambda_18*s[3],
      -lambda_30*s[4],
      -lambda_40*s[5],
      -lambda_50*s[6],
      -lambda_60*s[7],
      -lambda_70*s[8],  
       lambda_0*s[1]-sigma*e[1], #E-->Ip
       lambda_5*s[2]-sigma*e[2],
       lambda_18*s[3]-sigma*e[3],
       lambda_30*s[4]-sigma*e[4],
       lambda_40*s[5]-sigma*e[5],
       lambda_50*s[6]-sigma*e[6],
       lambda_60*s[7]-sigma*e[7],
       lambda_70*s[8]-sigma*e[8],  
                      sigma*e[1]-presmp*ip[1],   #Ip-----> [Is and Ia]
                      sigma*e[2]-presmp*ip[2],
                      sigma*e[3]-presmp*ip[3],
                      sigma*e[4]-presmp*ip[4],
                      sigma*e[5]-presmp*ip[5],
                      sigma*e[6]-presmp*ip[6],
                      sigma*e[7]-presmp*ip[7],
                      sigma*e[8]-presmp*ip[8],   
                                ((1-p_symp)*ip[1])-asymp*ia[1], #Ia --> R
                                ((1-p_symp)*ip[2])-asymp*ia[2],
                                ((1-p_symp)*ip[3])-asymp*ia[3],
                                ((1-p_symp)*ip[4])-asymp*ia[4],
                                ((1-p_symp)*ip[5])-asymp*ia[5],
                                ((1-p_symp)*ip[6])-asymp*ia[6],
                                ((1-p_symp)*ip[7])-asymp*ia[7],
                                ((1-p_symp)*ip[8])-asymp*ia[8],     
                                                   p_symp*ip[1]-p_hosp[1]*is[1]-((1-p_hosp[1])*asymp*is[1]),  #Is --> [H and R]
                                                   p_symp*ip[2]-p_hosp[2]*is[2]-((1-p_hosp[2])*asymp*is[2]),
                                                   p_symp*ip[3]-p_hosp[3]*is[3]-((1-p_hosp[3])*asymp*is[3]),
                                                   p_symp*ip[4]-p_hosp[4]*is[4]-((1-p_hosp[4])*asymp*is[4]),
                                                   p_symp*ip[5]-p_hosp[5]*is[5]-((1-p_hosp[5])*asymp*is[5]),
                                                   p_symp*ip[6]-p_hosp[6]*is[6]-((1-p_hosp[6])*asymp*is[6]),
                                                   p_symp*ip[7]-p_hosp[7]*is[7]-((1-p_hosp[7])*asymp*is[7]),
                                                   p_symp*ip[8]-p_hosp[8]*is[8]-((1-p_hosp[8])*asymp*is[8]),
                                                                p_hosp[1]*is[1]-p_icu[1]*h[1]-cc*h[1],     #H---->[C and R]
                                                                p_hosp[2]*is[2]-p_icu[2]*h[2]-cc*h[2],   
                                                                p_hosp[3]*is[3]-p_icu[3]*h[3]-cc*h[3],   
                                                                p_hosp[4]*is[4]-p_icu[4]*h[4]-cc*h[4],   
                                                                p_hosp[5]*is[5]-p_icu[5]*h[5]-cc*h[5],   
                                                                p_hosp[6]*is[6]-p_icu[6]*h[6]-cc*h[6],   
                                                                p_hosp[7]*is[7]-p_icu[7]*h[7]-cc*h[7],   
                                                                p_hosp[8]*is[8]-p_icu[8]*h[8]-cc*h[8],    
                                                                                p_icu[1]*h[1]-(1-mort)*cc*c[1]-mort*cc*c[1],  #C-->[R and D]
                                                                                p_icu[2]*h[2]-(1-mort)*cc*c[2]-mort*cc*c[2],
                                                                                p_icu[3]*h[3]-(1-mort)*cc*c[3]-mort*cc*c[3],
                                                                                p_icu[4]*h[4]-(1-mort)*cc*c[4]-mort*cc*c[4],
                                                                                p_icu[5]*h[5]-(1-mort)*cc*c[5]-mort*cc*c[5],
                                                                                p_icu[6]*h[6]-(1-mort)*cc*c[6]-mort*cc*c[6],
                                                                                p_icu[7]*h[7]-(1-mort)*cc*c[7]-mort*cc*c[7],
                                                                                p_icu[8]*h[8]-(1-mort)*cc*c[8]-mort*cc*c[8],
      (1-mort)*cc*c[1]+((1-p_hosp[1])*asymp*is[1])+asymp*ia[1]+cc*h[1],  #C+Is+H+Ia ------>R    
      (1-mort)*cc*c[2]+((1-p_hosp[2])*asymp*is[2])+asymp*ia[2]+cc*h[2],
      (1-mort)*cc*c[3]+((1-p_hosp[3])*asymp*is[3])+asymp*ia[3]+cc*h[3],
      (1-mort)*cc*c[4]+((1-p_hosp[4])*asymp*is[4])+asymp*ia[4]+cc*h[4],
      (1-mort)*cc*c[5]+((1-p_hosp[5])*asymp*is[5])+asymp*ia[5]+cc*h[5],
      (1-mort)*cc*c[6]+((1-p_hosp[6])*asymp*is[6])+asymp*ia[6]+cc*h[6],
      (1-mort)*cc*c[7]+((1-p_hosp[7])*asymp*is[7])+asymp*ia[7]+cc*h[7],
      (1-mort)*cc*c[8]+((1-p_hosp[8])*asymp*is[8])+asymp*ia[8]+cc*h[8],
      mort*cc*c[1],   #c-->dead
      mort*cc*c[2],
      mort*cc*c[3],
      mort*cc*c[4],
      mort*cc*c[5],
      mort*cc*c[6],
      mort*cc*c[7],
      mort*cc*c[8]) 
  )
}

require(deSolve)
## initial conditions
yinit <- c(
S0=887,
S5=7088,
S18=34314,
S30=29431,
S40=38043,
S50=44135,
S60=43274,
S70=66788,
E0=0,
E5=0,
E18=0,
E30=0,
E40=0,
E50=0,
E60=0,
E70=0,
IP0=0,
IP5=0,
IP18=0,
IP30=0,
IP40=0,
IP50=0,
IP60=0,
IP70=0,
IA0=0,
IA5=0,
IA18=0,
IA30=0,
IA40=1,
IA50=1,
IA60=1,
IA70=1,
IS0=0,
IS5=0,
IS18=0,
IS30=0,
IS40=0,
IS50=0,
IS60=0,
IS70=0,
H0=0,
H5=0,
H18=0,
H30=0,
H40=0,
H50=0,
H60=0,
H70=0,
C0=0,
C5=0,
C18=0,
C30=0,
C40=0,
C50=0,
C60=0,
C70=0,
R0=0,
R5=0,
R18=0,
R30=0,
R40=0,
R50=0,
R60=0,
R70=0,
D0=0,
D5=0,
D18=0,
D30=0,
D40=0,
D50=0,
D60=0,
D70=0
)
solve <- ode(
  y=yinit,
  times=seq(0,30,by=0.01),
  func=first.model
)
