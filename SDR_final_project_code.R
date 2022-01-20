library(dplyr)
library(ggplot2)
library(party)
library(caret)
library(e1071)
library(randomForest)
library(scatterplot3d)
library(rpart)

#################################################################################
#                     1) 데이터 불러오기 
#################################################################################


body <- read.csv("C:/Users/82105/Downloads/data/bodyPerformance.csv")
head(body)

sum(is.na(body)) #결측치는 0개
str(body) # 데이터 특성 살펴보기
body$class <- as.factor(body$class)

## 전체 데이터 중 random으로 100개 데이터만 추출
set.seed(2021)
male <- subset(body, gender=="M")
male <- male[sample(nrow(male),100),]
male <- male[,-2]
head(male)


#################################################################################
#                     2) EDA & 전처리 
#################################################################################


## 연속형 변수 히스토그램으로 그려서 특성 살펴보기
par.name <- names(male)
par(mfrow=c(2,2))
for(i in 1:4){hist(male[,i], main="", xlab=par.name[i])}
par(mfrow=c(2,2))
for(i in 5:8){hist(male[,i], main="", xlab=par.name[i])}
par(mfrow=c(2,2))
for(i in 9:10){hist(male[,i], main="", xlab=par.name[i])}

## 범주형 변수 barplot 그려서 특성 살펴보기
ggplot(male, aes(class))+geom_bar()+ggtitle("The Number of class")

##이상치 탐색 후 제거
boxplot(male[,1:10])$stats
male$broad.jump_cm <- ifelse(male$broad.jump_cm == 146, NA, male$broad.jump_cm)
male$broad.jump_cm <- ifelse(male$broad.jump_cm == 264, NA, male$broad.jump_cm)

male <- na.omit(male)
nrow(male)

## 충분차원축소 전 LCM 가정 만족하는지 확인
pairs(male)

## train/test split(original)
set.seed(2021)
sample_male = sample(1:nrow(male), size=round(0.8*nrow(male)))
train_male <- male[sample_male,]
test_male <- male[-sample_male,]

nrow(train_male)
nrow(test_male)


#################################################################################
#                      3) 충분 차원 축소
#################################################################################

y = unclass(train_male$class)
x = as.matrix(train_male[,1:10])


### sir, save, dr, phd, iht method 함수 정의

sir=function(x,y,h,r,ytype){
  p=ncol(x);n=nrow(x)
  signrt=matpower(var(x),-1/2)
  xc=t(t(x)-apply(x,2,mean))
  xst=xc%*%signrt
  if(ytype=="continuous") ydis=discretize(y,h)
  if(ytype=="categorical") ydis=discretize(y,h)
  yless=ydis;ylabel=numeric()
  for(i in 1:n) {if(var(yless)!=0) {ylabel=c(ylabel,yless[1]);yless=yless[yless!=yless[1]]}}
  ylabel=c(ylabel,yless[1])
  prob=numeric();exy=numeric()
  for(i in 1:h) prob=c(prob,length(ydis[ydis==ylabel[i]])/n) 
  for(i in 1:h) exy=rbind(exy,apply(xst[ydis==ylabel[i],],2,mean))
  sirmat=t(exy)%*%diag(prob)%*%exy
  return(list(beta=signrt%*%eigen(sirmat)$vectors[,1:r],sirmat=sirmat))}


save=function(x,y,h,r,ytype){
  p=ncol(x);n=nrow(x)
  signrt=matpower(var(x),-1/2)
  xc=t(t(x)-apply(x,2,mean))
  xst=xc%*%signrt
  if(ytype=="continuous") ydis=discretize(y,h)
  if(ytype=="categorical") ydis=discretize(y,h)
  ylabel=unique(ydis)
  prob=numeric() 
  for(i in 1:h) prob=c(prob,length(ydis[ydis==ylabel[i]])/n)
  vxy = array(0,c(p,p,h))
  for(i in 1:h) vxy[,,i] = var(xst[ydis==ylabel[i],]) 
  savemat=0
  for(i in 1:h){
    savemat=savemat+prob[i]*(vxy[,,i]-diag(p))%*%(vxy[,,i]-diag(p))}
  return(list(beta=signrt%*%eigen(savemat)$vectors[,1:r],savemat=savemat))}



dr=function(x,y,h,r,ytype){
  p=ncol(x);n=nrow(x)
  signrt=matpower(var(x),-1/2)
  xc=t(t(x)-apply(x,2,mean))
  xst=xc%*%signrt
  if(ytype=="continuous") ydis=discretize(y,h)
  if(ytype=="categorical") ydis=discretize(y,h)
  ylabel=unique(ydis)
  prob=numeric() 
  for(i in 1:h) prob=c(prob,length(ydis[ydis==ylabel[i]])/n)
  vxy = array(0,c(p,p,h));exy=numeric()
  for(i in 1:h) {
    vxy[,,i]=var(xst[ydis==ylabel[i],])
    exy=rbind(exy,apply(xst[ydis==ylabel[i],],2,mean))}
  mat1 = matrix(0,p,p);mat2 = matrix(0,p,p)
  for(i in 1:h){
    mat1 = mat1+prob[i]*(vxy[,,i]+exy[i,]%*%t(exy[i,]))%*%
      (vxy[,,i]+exy[i,]%*%t(exy[i,]))
    mat2 = mat2+prob[i]*exy[i,]%*%t(exy[i,])}
  out = 2*mat1+2*mat2%*%mat2+2*sum(diag(mat2))*mat2-2*diag(p)
  return(list(beta=signrt%*%eigen(out)$vectors[,1:r],drmat=out))
}


phd = function(x,y,r){
  matpower=function(a,alpha){
    a=(a+t(a))/2;tmp=eigen(a)
    return(tmp$vectors%*%diag((tmp$values)^alpha)%*%t(tmp$vectors))}
  n=length(y);signrt=matpower(var(x),-1/2)
  z = center(x)%*%signrt
  return(list(beta=signrt%*%eigen(t(z*(y-mean(y)))%*%z/n)$vectors[,1:r],phdmat=t(z*(y-mean(y)))%*%z/n))}


iht=function(x,y,r){
  matpower=function(a,alpha){
    a=(a+t(a))/2;tmp=eigen(a)
    return(tmp$vectors%*%diag((tmp$values)^alpha)%*%t(tmp$vectors))}
  standmat=function(x){
    mu=apply(x,2,mean);sig=var(x);signrt=matpower(sig,-1/2)
    return(t(t(x)-mu)%*%signrt)}
  z=standmat(x);szy=cov(z,y);szz=var(z);p=dim(z)[2];imat=szy
  for(i in 1:(p-1)) imat=cbind(imat,matpower(szz,i)%*%szy)
  return(list(beta=eigen(imat%*%t(imat))$vectors[,1:r],ihtmat=imat%*%t(imat)))}



### Order Determination

## 1) sequential test

# <SIR>

################################################################
#          Power of matrix
################################################################
matpower=function(a,alpha){
  a = (a + t(a))/2
  tmp = eigen(a)
  return(tmp$vectors%*%diag((tmp$values)^alpha)%*%
           t(tmp$vectors))}

##############################################################
#      Center X (n by p matrix)        
##############################################################
center = function(x){
  return(t(t(x)-apply(x,2,mean)))}

################################################################
#           discretize
################################################################
discretize=function(y,h){
  n=length(y);m=round(n/h)
  y=y+.00001*mean(y)*rnorm(n)
  yord = y[order(y)]
  divpt=numeric();for(i in 1:(h-1)) divpt = c(divpt,yord[i*m+1])
  y1=rep(0,n);y1[y<divpt[1]]=1;y1[y>=divpt[h-1]]=h
  for(i in 2:(h-1)) y1[(y>=divpt[i-1])&(y<divpt[i])]=i
  return(y1)
}

################################################################
#          distance between subspaces
################################################################
dist=function(v1,v2){
  v1=as.matrix(v1);v2=as.matrix(v2)
  if(dim(v1)[1]>1){
    p1 <- v1%*%matpower(t(v1)%*%v1,-1)%*%t(v1)
    p2 <- v2%*%matpower(t(v2)%*%v2,-1)%*%t(v2)
  }
  if(dim(v1)[1]==1){
    p1=v1%*%t(v1)/c(t(v1)%*%v1)
    p2=v2%*%t(v2)/c(t(v2)%*%v2)}
  d <- sqrt(sum((p1-p2)*(p1-p2)))
  return(d)
}

##############################################################
#                   symmtrize a matrix
############################################################## 
symmetry = function(a){
  return((a + t(a))/2)}



###############################################################
#                    sir sequential test                        
###############################################################
seqtestsir=function(x,y,h,r,ytype){
  p=ncol(x);n=nrow(x)
  signrt=matpower(var(x),-1/2)
  xc=t(t(x)-apply(x,2,mean))
  xst=xc%*%signrt
  if(ytype=="continuous") ydis=discretize(y,h)
  if(ytype=="categorical") ydis=discretize(y,h)
  yless=ydis;ylabel=numeric()
  for(i in 1:n) {if(var(yless)!=0) {ylabel=c(ylabel,yless[1]);yless=yless[yless!=yless[1]]}}
  ylabel=c(ylabel,yless[1])
  prob=numeric();exy=numeric()
  for(i in 1:h) prob=c(prob,length(ydis[ydis==ylabel[i]])/n) 
  for(i in 1:h) exy=rbind(exy,apply(xst[ydis==ylabel[i],],2,mean))
  sirmat=t(exy)%*%diag(prob)%*%exy
  test=n*sum(eigen(sirmat)$values[(r+1):p])
  pval=1-pchisq(test,(p-r)*(h-1-r))
  return(pval)}


########################################################################
#                 sequential SAVE test 
########################################################################
seqtestsave=function(x,y,h,r,ytype){
  p=ncol(x);n=nrow(x)
  xst=t(t(x)-apply(x,2,mean))%*%matpower(var(x),-1/2)
  if(ytype=="continuous") ydis=discretize(y,h)
  if(ytype=="categorical") ydis=discretize(y,h)
  yless=ydis;ylabel=numeric()
  for(i in 1:n) {
    if(var(yless)!=0){
      ylabel=c(ylabel,yless[1]);yless=yless[yless!=yless[1]]}}
  ylabel=c(ylabel,yless[1])
  sk=matrix(0,n,h)
  for(i in 1:n) for(k in 1:h) {
    if(ydis[i]==ylabel[k]) sk[i,k]=1
    if(ydis[i]!=ylabel[k]) sk[i,k]=0}
  prob=numeric()
  for(i in 1:h) prob=c(prob,length(ydis[ydis==ylabel[i]])/n)
  muk=numeric()
  for(i in 1:h) muk = rbind(muk,apply(xst[ydis==ylabel[i],],2,mean))
  vxy = array(0,c(p,p,h))
  for(i in 1:h) vxy[,,i]=var(xst[ydis==ylabel[i],])
  mmat=numeric();for(i in 1:h) mmat=cbind(mmat,prob[i]^(1/2)*(diag(p)-vxy[,,i]))
  tmp=svd(mmat);uu=tmp$u[,1:r];vv=tmp$v[,1:r]
  qmat=diag(p)-uu%*%t(uu);qmatmt=diag(p*h)-vv%*%t(vv)
  qmstqmt=array(0,c(n,p,p*h))
  for(i in 1:n){
    u1=numeric();for(k in 1:h) u1=c(u1,prob[k]^(-1/2)*(prob[k]-sk[i,k]))
    u2=numeric();for(k in 1:h) u2=c(u2,prob[k]^(-1/2)*sk[i,k]*muk[k,])
    mat1=qmat%*%kronecker(t(u1),(xst[i,]%*%t(xst[i,])-diag(p)))%*%qmatmt
    mat2=qmat%*%xst[i,]%*%t(u2)%*%qmatmt
    qmstqmt[i,,]=mat1+mat2}
  vecqmstqmt=numeric()
  for(i in 1:n) vecqmstqmt=rbind(vecqmstqmt,c(qmstqmt[i,,]))
  vmat=var(vecqmstqmt);omega=eigen(vmat)$values[1:((p-r)*(p*h-r))]
  teststat=n*sum((svd(mmat)$d[(r+1):p])^2)
  obs=numeric();nsim=20000
  for(isim in 1:nsim) {
    ki=rnorm(length(omega))^2;obs=c(obs,sum(omega*ki))}
  pval=length((1:nsim)[obs>teststat])/nsim;return(pval)
}


###########################################################################
#      sequential test for directional regression
###########################################################################
seqtestdr=function(x,y,h,r,ytype){
  p=ncol(x);n=nrow(x);h=8
  xc=t(t(x)-apply(x,2,mean))
  if(ytype=="categorical") ydis=discretize(y,h)
  yless=ydis;ylabel=numeric()
  for(i in 1:n) {
    if(var(yless)!=0){
      ylabel=c(ylabel,yless[1]);yless=yless[yless!=yless[1]]}}
  ylabel=c(ylabel,yless[1])
  sk=matrix(0,n,h); for(i in 1:n) for(k in 1:h)  if(ydis[i]==ylabel[k]) sk[i,k]=1
  pk=apply(sk,2,mean)
  sig=var(xc)
  uk=numeric(); for(i in 1:h) uk=rbind(uk,apply(xc[ydis==ylabel[i],],2,mean))
  vk=array(0,c(p,p,h)); for(i in 1:h) vk[,,i]=var(xc[ydis==ylabel[i],])-sig
  m1=numeric(); for(k in 1:h) m1=cbind(m1,pk[k]^(1/2)*vk[,,k])
  m2=t(uk)%*%diag(pk)%*%uk
  tr=function(a) return(sum(diag(a)))
  m3=numeric(); for(k in 1:h) m3=cbind(m3,pk[k]^(1/2)*(tr(m2))^(1/2)*uk[k,])
  m=cbind(m1,m2,m3)
  pkst=numeric(); for(i in 1:n) pkst=rbind(pkst,sk[i,]-pk)
  ukst=array(0,c(p,h,n)); for(i in 1:n) for(k in 1:h) {
    ukst[,k,i]=(xc[i,]-uk[k,])*sk[i,k]/pk[k]-xc[i,]}
  vkst=array(0,c(p,p,h,n)); for(k in 1:h) for(i in 1:n) {
    vkst[,,k,i]=(xc[i,]%*%t(xc[i,])-sig-vk[,,k])*sk[i,k]/pk[k]-uk[k,]%*%t(xc[i,])-
      xc[i,]%*%t(uk[k,])-xc[i,]%*%t(xc[i,])+sig}
  m1kst=array(0,c(p,p,h,n)); for(k in 1:h) for(i in 1:n) {
    m1kst[,,k,i]=(1/2)*pk[k]^(-1/2)*pkst[i,k]*vk[,,k]+pk[k]^(1/2)*vkst[,,k,i]}
  m2st=array(0,c(p,p,n)); for(i in 1:n){ 
    for(k in 1:h) {
      m2st[,,i]=m2st[,,i]+pkst[i,k]*uk[k,]%*%t(uk[k,])+pk[k]*ukst[,k,i]%*%t(uk[k,])+
        pk[k]*uk[k,]%*%t(ukst[,k,i])}}
  m3kst=array(0,c(p,h,n)); for(k in 1:h) for(i in 1:n){
    m3kst[,k,i]=(1/2)*pk[k]^(-1/2)*pkst[i,k]*(tr(m2))^(1/2)*uk[k,]+
      (1/2)*pk[k]^(1/2)*(tr(m2))^(-1/2)*tr(m2st[,,i])*uk[k,]+
      pk[k]^(1/2)*(tr(m2))^(1/2)*ukst[,k,i]}
  mst=array(0,c(p,p*h+p+h,n)); for(i in 1:n){
    mst1=numeric(); for(k in 1:h) mst1=cbind(mst1,m1kst[,,k,i]) 
    mst3=numeric(); for(k in 1:h) mst3=cbind(mst3,m3kst[,k,i])
    mst[,,i]=cbind(mst1,m2st[,,i],mst3)}
  if(r==0) qlef=diag(p);qrig=diag(p*h+p+h)
  svdm=svd(m);u1=svdm$u[,1:r];v1=svdm$v[,1:r]
  qlef=diag(p)-u1%*%t(u1);qrig=diag(p*h+p+h)-v1%*%t(v1)
  qmstq=array(0,c(p,p*h+p+h,n)); for(i in 1:n) qmstq[,,i]=qlef%*%mst[,,i]%*%qrig
  vqmstq=matrix(0,n,p*(p*h+p+h)); for(i in 1:n) vqmstq[i,]=c(qmstq[,,i])
  s=var(vqmstq);omega=eigen(s)$values[1:((p-r)*(p*h+p+h-r))]
  teststat=n*sum(eigen(m%*%t(m))$values[(r+1):p])
  obs=numeric();nsim=20000
  for(isim in 1:nsim) {
    ki=rnorm(length(omega))^2;obs=c(obs,sum(omega*ki))}
  pval=length((1:nsim)[obs>teststat])/nsim;return(pval)
}


###########################################################################
#      sequential test for phd
###########################################################################
seqtestphd=function(x,y,r){
  matpower=function(a,alpha){
    a=(a+t(a))/2;tmp=eigen(a)
    return(tmp$vectors%*%diag((tmp$values)^alpha)%*%t(tmp$vectors))}
  n=length(y);p=ncol(x);signrt=matpower(var(x),-1/2)
  z = center(x)%*%signrt
  phdmat=t(z)%*%diag(y-mean(y))%*%z/n; phdmat=phdmat%*%phdmat  
  test=n*sum((eigen(phdmat)$values[(r+1):p]))/(2*var(y))
  pval=1-pchisq(test,(p-r+1)*(p-r)/2)
  return(list(pval=pval,test=test))
}


###########################################################################
#      sequential test for iht
###########################################################################
seqtestiht=function(x,y,r){
  matpower=function(a,alpha){
    a=(a+t(a))/2;tmp=eigen(a)
    return(tmp$vectors%*%diag((tmp$values)^alpha)%*%t(tmp$vectors))}
  standmat=function(x){
    mu=apply(x,2,mean);sig=var(x);signrt=matpower(sig,-1/2)
    return(t(t(x)-mu)%*%signrt)}
  z=standmat(x);szy=cov(z,y);szz=var(z);p=dim(z)[2];imat=szy
  for(i in 1:(p-1)) imat=cbind(imat,matpower(szz,i)%*%szy)
  ihtmat=imat%*%t(imat)
  test=n*sum((eigen(ihtmat)$values[(r+1):p]))
  pval=1-pchisq(test,(p-r+1))
  return(pval)
}

#######################################################################
#            apply sequential test 
#########################################################################

y = unclass(train_male$class)
x = as.matrix(train_male[,1:10])
p=ncol(x);n=nrow(x);h=8

print("--------------sir-----------------------")
for(r in 0:6){
  pval = seqtestsir(x,y,h,r,"categorical")
  print(round(pval,2))
}

print("--------------save-----------------------")

for(r in 0:7){
  pval = seqtestsave(x,y,h,r,"categorical")
  print(round(pval,2))
}
print("--------------dr-----------------------")

for(r in 0:7){
  pval = seqtestdr(x,y,h,r,"categorical")
  print(round(pval,2))
}
print("-------------phd------------------------")

for(r in 0:7){
  pval = seqtestphd(x,y,r)$pval
  print(round(pval,2))
}
print("--------------iht-----------------------")

for(r in 0:7){
  pval = seqtestiht(x,y,r)
  print(round(pval,2))
}

# <bic type criteria>


bic=function(x,y,h,ytype,criterion,method){
  maximizer=function(x,y) return(x[order(y)[length(y)]])
  r=2;n=dim(x)[1];p=dim(x)[2]
  if(method=="sir") candmat=sir(x,y,h,r,ytype)$sirmat
  if(method=="save") candmat=save(x,y,h,r,ytype)$savemat
  if(method=="dr") candmat=dr(x,y,h,r,ytype)$drmat
  out=eigen(candmat);lam=out$values
  if(criterion=="lal"){
    gn=numeric();for(k in 0:p){
      if(k==0) gn=c(gn,0) else
        gn=c(gn,sum(lam[1:k])-(2*lam[1])*n^(-1/2)*(log(n))^(1/2)*k)}}
  if(criterion=="zmp"){
    gn=numeric();for(k in 0:(p-1)){
      c1=(lam[1]/3)*(0.5* log(n)+0.1* n^(1/3))/(2*n)
      c2=k*(2*p-k+1)
      gn=c(gn,sum(log(lam[(k+1):p]+1)-lam[(k+1):p])-c1*c2)}
    gn=c(gn,-c1*p*(2*p-p+1))}
  return(list(rhat=maximizer(0:p,gn),rcurve=gn))
}


bic2=function(x,y,criterion,method){
  maximizer=function(x,y) return(x[order(y)[length(y)]])
  r=2;n=dim(x)[1];p=dim(x)[2]
  if(method=="phd") candmat=phd(x,y,r)$phdmat
  if(method=="iht") candmat=iht(x,y,r)$ihtmat
  out=eigen(candmat);lam=out$values
  if(criterion=="lal"){
    gn=numeric();for(k in 0:p){
      if(k==0) gn=c(gn,0) else
        gn=c(gn,sum(lam[1:k])-(2*lam[1])*n^(-1/2)*(log(n))^(1/2)*k)}}
  if(criterion=="zmp"){
    gn=numeric();for(k in 0:(p-1)){
      c1=(lam[1]/3)*(0.5* log(n)+0.1* n^(1/3))/(2*n)
      c2=k*(2*p-k+1)
      gn=c(gn,sum(log(lam[(k+1):p]+1)-lam[(k+1):p])-c1*c2)}
    gn=c(gn,-c1*p*(2*p-p+1))}
  return(list(rhat=maximizer(0:p,gn),rcurve=gn))
}


#sir; lal criterion
bic(x,y,8,"categorical","lal","sir")
bic(x,y,8,"categorical","lal","save")
bic(x,y,8,"categorical","lal","dr")
bic2(x,y,"lal","phd")
bic2(x,y,"lal","iht")


# <ye-weiss method>
yw=function(x,y,kmax,nboot,method){
  r=2;n=dim(x)[1];p=dim(x)[2];h=8;ytype="categorical"
  candmat=function(x,y,r,method){
    if(method=="sir") mat=sir(x,y,h,r,ytype)$sirmat
    if(method=="save") mat=save(x,y,h,r,ytype)$savemat
    if(method=="dr") mat=dr(x,y,h,r,ytype)$drmat
    if(method=="phd") mat=phd(x,y,r)$phdmat
    if(method=="iht") mat=iht(x,y,r)$ihtmat
    return(mat)}
  out=candmat(x,y,r,method)
  eval.full=eigen(out)$values;evec.full=eigen(out)$vectors
  prepare=function(kmax,evec1,evec2){
    out=numeric();for(k in 1:kmax){
      if(k==1) out=c(out,1-abs(t(evec1[,1])%*%evec2[,1]))
      if(k!=1) out=c(out,1-abs(det(t(evec1[,1:k])%*%evec2[,1:k])))}
    return(out)}
  yw.out=0;for(iboot in 1:nboot){
    bootindex=round(runif(n,min=-0.5,max=n+0.5))
    xs=x[bootindex,];ys=y[bootindex]
    mat=candmat(xs,ys,r,method);evec=eigen(mat)$vectors
    yw.out=yw.out+prepare(kmax,evec.full,evec)/nboot}
  return(yw.out)
}


print(round(yw(x,y,6,200,"sir"),3))
print(round(yw(x,y,7,200,"save"),3))
print(round(yw(x,y,7,200,"dr"),3))
print(round(yw(x,y,7,200,"phd"),3))
print(round(yw(x,y,7,200,"iht"),3))


# <ladle estimator>
###############################################################
#          ladle estimator for sir, save, dr
###############################################################
ladle=function(x,y,h,nboot,method,ytype){
  r=2;n=dim(x)[1];p=dim(x)[2] 
  if(p<=10) kmax=p-2;if(p>10) kmax=floor(p/log(p)) 
  candmat=function(x,y,h,r,ytype,method){
    if(method=="sir") mat=sir(x,y,h,r,ytype)$sirmat
    if(method=="save") mat=save(x,y,h,r,ytype)$savemat
    if(method=="dr") mat=dr(x,y,h,r,ytype)$drmat
    return(mat)}
  phin=function(kmax,eval){den=1+sum(eval[1:(kmax+1)]);return(eval[1:(kmax+1)]/den)}
  out=candmat(x,y,h,r,ytype,method)
  eval.full=eigen(out)$values;evec.full=eigen(out)$vectors
  pn=phin(kmax,eval.full)
  prefn0=function(kmax,evec1,evec2){
    out=numeric();for(k in 0:kmax){
      if(k==0) out=c(out,0)
      if(k==1) out=c(out,1-abs(t(evec1[,1])%*%evec2[,1]))
      if(k!=0&k!=1) out=c(out,1-abs(det(t(evec1[,1:k])%*%evec2[,1:k])))}
    return(out)}
  fn0=0
  for(iboot in 1:nboot){ 
    bootindex=round(runif(n,min=-0.5,max=n+0.5))
    xs=x[bootindex,];ys=y[bootindex]
    mat=candmat(xs,ys,h,r,ytype,method);eval=eigen(mat)$values;evec=eigen(mat)$vectors
    fn0=fn0+prefn0(kmax,evec.full,evec)/nboot}
  minimizer=function(a,b) return(a[order(b)][1])
  fn=fn0/(1+sum(fn0));gn=pn+fn;rhat=minimizer(0:kmax,gn)
  return(list(kset=(0:kmax),gn=gn,rhat=rhat))
}



###############################################################
#          ladle estimator for phd, iht
###############################################################
ladle2=function(x,y,nboot,method){
  r=2;n=dim(x)[1];p=dim(x)[2] 
  if(p<=10) kmax=p-2;if(p>10) kmax=floor(p/log(p)) 
  candmat=function(x,y,r,method){
    if(method=="phd") mat=phd(x,y,r)$phdmat
    if(method=="iht") mat=iht(x,y,r)$ihtmat
    return(mat)}
  phin=function(kmax,eval){den=1+sum(eval[1:(kmax+1)]);return(eval[1:(kmax+1)]/den)}
  out=candmat(x,y,r,method)
  eval.full=eigen(out)$values;evec.full=eigen(out)$vectors
  pn=phin(kmax,eval.full)
  prefn0=function(kmax,evec1,evec2){
    out=numeric();for(k in 0:kmax){
      if(k==0) out=c(out,0)
      if(k==1) out=c(out,1-abs(t(evec1[,1])%*%evec2[,1]))
      if(k!=0&k!=1) out=c(out,1-abs(det(t(evec1[,1:k])%*%evec2[,1:k])))}
    return(out)}
  fn0=0
  for(iboot in 1:nboot){ 
    bootindex=round(runif(n,min=-0.5,max=n+0.5))
    xs=x[bootindex,];ys=y[bootindex]
    mat=candmat(xs,ys,r,method);eval=eigen(mat)$values;evec=eigen(mat)$vectors
    fn0=fn0+prefn0(kmax,evec.full,evec)/nboot}
  minimizer=function(a,b) return(a[order(b)][1])
  fn=fn0/(1+sum(fn0));gn=pn+fn;rhat=minimizer(0:kmax,gn)
  return(list(kset=(0:kmax),gn=gn,rhat=rhat))
}



out=ladle(x,y,8,200,"sir","categorical");kset=out$kset;gn=out$gn
plot(kset,gn,type="l",xlab="k")

out=ladle(x,y,8,200,"save","categorical");kset=out$kset;gn=out$gn
plot(kset,gn,type="l",xlab="k")

out=ladle(x,y,8,200,"dr","categorical");kset=out$kset;gn=out$gn
plot(kset,gn,type="l",xlab="k")

out=ladle2(x,y,200,"phd");kset=out$kset;gn=out$gn
plot(kset,gn,type="l",xlab="k")

out=ladle2(x,y,200,"iht");kset=out$kset;gn=out$gn
plot(kset,gn,type="l",xlab="k")


# <결정된 차원으로 차원 축소>
  
#1) sir

##############################################################
#                         apply sir
##############################################################
h=8;r=2;ytype="categorical";beta=sir(x,y,h,r,ytype)$beta
pred_sir = center(x) %*% beta 

par(mfrow=c(1,2))
df1 <- as.data.frame(cbind(pred_sir, train_male$class))
plot(df1$V1, df1$V3)
plot(df1$V2, df1$V3)

##############################################################
#                        apply sir - train, test
##############################################################
h=8;r=1;ytype="categorical";beta=sir(x,y,h,r,ytype)$beta
train_x_sir = center(x) %*% beta
test_x_sir= center(as.matrix(test_male[,1:10])) %*% beta

train_sir=as.data.frame(cbind(train_x_sir, train_male$class))
test_sir=as.data.frame(cbind(test_x_sir, test_male$class))

#2) save
##############################################################
#                         apply save
##############################################################
h=8;r=4;ytype="categorical";beta=save(x,y,h,r,ytype)$beta
pred_save = center(x) %*% beta 

par(mfrow=c(2,2))
df2 <- as.data.frame(cbind(pred_save, train_male$class))
plot(df2$V1, df2$V5)
plot(df2$V2, df2$V5)
plot(df2$V3, df2$V5)
plot(df2$V4, df2$V5)

##############################################################
#                        apply save - train, test
##############################################################
h=8;r=4;ytype="categorical";beta=save(x,y,h,r,ytype)$beta
train_x_save= center(x) %*% beta
test_x_save= center(as.matrix(test_male[,1:10])) %*% beta

train_save=as.data.frame(cbind(train_x_save, train_male$class))
test_save=as.data.frame(cbind(test_x_save, test_male$class))

#3) dr
##############################################################
#                         apply dr
##############################################################
h=8;r=6;ytype="categorical";beta=dr(x,y,h,r,ytype)$beta
pred_dr = center(x) %*% beta 

par(mfrow=c(2,3))
df3 <- as.data.frame(cbind(pred_dr, train_male$class))
plot(df3$V1, df3$V7)
plot(df3$V2, df3$V7)
plot(df3$V3, df3$V7)
plot(df3$V4, df3$V7)
plot(df3$V5, df3$V7)
plot(df3$V6, df3$V7)


##############################################################
#                        apply dr - train, test
##############################################################
h=8;r=1;ytype="categorical";beta=dr(x,y,h,r,ytype)$beta
train_x_dr = center(x) %*% beta
test_x_dr= center(as.matrix(test_male[,1:10])) %*% beta

train_dr=as.data.frame(cbind(train_x_dr, train_male$class))
test_dr=as.data.frame(cbind(test_x_dr, test_male$class))

#4) phd
##############################################################
#                         apply phd
##############################################################
r=3;beta=phd(x,y,r)$beta
pred_phd = center(x) %*% beta 

par(mfrow=c(1,3))
df4 <- as.data.frame(cbind(pred_phd, train_male$class))
plot(df4$V1, df4$V4)
plot(df4$V2, df4$V4)
plot(df4$V3, df4$V4)


##############################################################
#                        apply phd - train, test
##############################################################
r=3;beta=phd(x,y,r)$beta
train_x_phd = center(x) %*% beta
test_x_phd= center(as.matrix(test_male[,1:10])) %*% beta

train_phd=as.data.frame(cbind(train_x_phd, train_male$class))
test_phd=as.data.frame(cbind(test_x_phd, test_male$class))

#5) iht
##############################################################
#                         apply iht
##############################################################
r=2;beta=iht(x,y,r)$beta
pred_iht = center(x) %*% beta 

par(mfrow=c(1,2))
df5 <- as.data.frame(cbind(pred_iht, train_male$class))
plot(df5$V1, df5$V3)
plot(df5$V2, df5$V3)


##############################################################
#                        apply iht - train, test
##############################################################
r=1;beta=iht(x,y,r)$beta
par(mfrow=c(2,2))
train_x_iht = center(x) %*% beta
test_x_iht= center(as.matrix(test_male[,1:10])) %*% beta

train_iht=as.data.frame(cbind(train_x_iht, train_male$class))
test_iht=as.data.frame(cbind(test_x_iht, test_male$class))


#################################################################################
#                      4) 모형 적합 - decision tree, svm model 
#################################################################################

#<decision tree>

# original
dt1 <- rpart(class~., data=train_male)
test_predict <- predict(dt1, test_male,type="class")
confusionMatrix(test_male$class, test_predict,positive = "pos")


# sir
dt2 <- rpart(as.factor(V2)~., data=train_sir)
test_predict_sir <- predict(dt2, test_sir, type="class")
confusionMatrix(as.factor(test_sir$V2), test_predict_sir,positive = "pos")

# save 
dt3 <- rpart(as.factor(V5)~., data=train_save)
test_predict_save<- predict(dt3, test_save, type="class")
confusionMatrix(as.factor(test_save$V5), test_predict_save,positive = "pos")

# dr
dt4 <- rpart(as.factor(V2)~., data=train_dr)
test_predict_dr<- predict(dt4, test_dr, type="class")
confusionMatrix(as.factor(test_dr$V2), test_predict_dr,positive = "pos")

# phd
dt5 <- rpart(as.factor(V4)~., data=train_phd)
test_predict_phd<- predict(dt5, test_phd, type="class")
confusionMatrix(as.factor(test_phd$V4), test_predict_phd,positive = "pos")

# iht
dt6<- rpart(as.factor(V2)~., data=train_iht)
test_predict_iht<- predict(dt6, test_iht, type="class")
confusionMatrix(as.factor(test_iht$V2), test_predict_iht,positive = "pos")

#<svm>
# original
svm1 <- svm(class~., data=train_male)
test_predict <- predict(svm1, test_male)
confusionMatrix(test_male$class, test_predict,positive = "pos")


# sir
svm2 <- svm(as.factor(V2)~., data=train_sir)
test_predict_sir <- predict(svm2, test_sir, type="class")
confusionMatrix(as.factor(test_sir$V2), test_predict_sir,positive = "pos")

# save
svm3 <- svm(as.factor(V5)~., data=train_save)
test_predict_save<- predict(svm3, test_save, type="class")
confusionMatrix(as.factor(test_save$V5), test_predict_save,positive = "pos")

# dr
svm4 <- svm(as.factor(V2)~., data=train_dr)
test_predict_dr<- predict(svm4, test_dr, type="class")
confusionMatrix(as.factor(test_dr$V2), test_predict_dr,positive = "pos")

# phd
svm5 <- svm(as.factor(V4)~., data=train_phd)
test_predict_phd<- predict(svm5, test_phd, type="class")
confusionMatrix(as.factor(test_phd$V4), test_predict_phd,positive = "pos")

# iht
svm6<- svm(as.factor(V2)~., data=train_iht)
test_predict_iht<- predict(svm6, test_iht, type="class")
confusionMatrix(as.factor(test_iht$V2), test_predict_iht,positive = "pos")

