set A;
set P := {i in A, j in A : i<j};
param n >= 0;
param d >= 0;
param radius >= 0;
param PI := 3.141592;
param v0{A};
param cap{A};
param qR{A} default 1;

param theta0{i in A} := if cap[i] >= PI then cap[i] - 2*PI else cap[i];
param vx0{i in A} := v0[i]*cos(theta0[i]);
param vy0{i in A} := v0[i]*sin(theta0[i]);
param vax{i in A} := if theta0[i] >= PI then qR[i]*v0[i]*cos(theta0[i] - 2*PI) else qR[i]*v0[i]*cos(theta0[i]);
param vay{i in A} := if theta0[i] >= PI then qR[i]*v0[i]*sin(theta0[i] - 2*PI) else qR[i]*v0[i]*sin(theta0[i]);
param vrx0{i in A, j in A : i<j} := v0[i]*cos(theta0[i]) - v0[j]*cos(theta0[j]);
param vry0{(i,j) in P} := v0[i]*sin(theta0[i]) - v0[j]*sin(theta0[j]);
param x0{i in A} default -radius*cos((i-1)*2*PI/n + PI);
param y0{i in A} default -radius*sin((i-1)*2*PI/n + PI);
param xr0{(i,j) in P} := x0[i]-x0[j];
param yr0{(i,j) in P} := y0[i]-y0[j];
param tm0{(i,j) in P} := -(xr0[i,j]*vrx0[i,j] + yr0[i,j]*vry0[i,j])/(vrx0[i,j]**2 + vry0[i,j]**2);

param vrax{(i,j) in P} := v0[i]*cos(theta0[i]) - qR[j]*v0[j]*cos(theta0[j]);
param vray{(i,j) in P} := v0[i]*sin(theta0[i]) - qR[j]*v0[j]*sin(theta0[j]);
param varx{(i,j) in P} := qR[i]*v0[i]*cos(theta0[i]) - v0[j]*cos(theta0[j]);
param vary{(i,j) in P} := qR[i]*v0[i]*sin(theta0[i]) - v0[j]*sin(theta0[j]);
param vrry{(i,j) in P} := v0[i]*sin(theta0[i]) - v0[j]*sin(theta0[j]);
param vrrx{(i,j) in P} := v0[i]*cos(theta0[i]) - v0[j]*cos(theta0[j]);
param sep0{(i,j) in P} := (yr0[i,j]**2 - d**2)*vrrx[i,j]**2 + (xr0[i,j]**2 - d**2)*vrry[i,j]**2 - 2*vrrx[i,j]*vrry[i,j]*xr0[i,j]*yr0[i,j];
param qmin := 0.5;
param qmax := 1.5;
param qdev;
param alpha default 1e-6;

param a{(i,j) in P} := yr0[i,j]**2 - d**2;
param b{(i,j) in P} := xr0[i,j]**2 - d**2;
param c{(i,j) in P} := 2*xr0[i,j]*yr0[i,j];

#-----ACTION------------------------------------------------------------------------------------
param Mbin1 {(i,j) in P};
param Mbin311 {(i,j) in P : xr0[i,j] >=0 and yr0[i,j] < 0};
param Mbin312 {(i,j) in P : xr0[i,j] >=0 and yr0[i,j] < 0};
param Mbin321 {(i,j) in P : xr0[i,j] < 0 and yr0[i,j] >=0};
param Mbin322 {(i,j) in P : xr0[i,j] < 0 and yr0[i,j] >=0};
param Mbin331 {(i,j) in P : xr0[i,j] >=0 and yr0[i,j] >=0};
param Mbin332 {(i,j) in P : xr0[i,j] >=0 and yr0[i,j] >=0};
param Mbin341 {(i,j) in P : xr0[i,j] < 0 and yr0[i,j] < 0};
param Mbin342 {(i,j) in P : xr0[i,j] < 0 and yr0[i,j] < 0};
param uvrx{(i,j) in P} := qmax*(v0[i] + v0[j]);
param uvry{(i,j) in P} := qmax*(v0[i] + v0[j]);
param lvrx{(i,j) in P} := -qmax*(v0[i] + v0[j]);
param lvry{(i,j) in P} := -qmax*(v0[i] + v0[j]);

var q{i in A} >= qmin <= qmax;
var vrx{(i,j) in P} >= lvrx[i,j] <= uvrx[i,j];
var vry{(i,j) in P} >= lvry[i,j] <= uvry[i,j];
var z{(i,j) in P} binary;
var delta{i in A} binary;
var Q >=0;

minimize Dev: (Q + alpha*(sum{i in A} (delta[i])));

s.t. cq{i in A}: Q >= (1-q[i])**2;
s.t. turnlb{i in A}: (q[i]) >= (delta[i])*(qmin) + (1-delta[i]);
s.t. turnub{i in A}: (q[i]) <= (delta[i])*(qmax) + (1-delta[i]);

s.t. cvrx{(i,j) in P} : vrx[i,j] = q[i]*v0[i]*cos(theta0[i]) - q[j]*v0[j]*cos(theta0[j]);
s.t. cvry{(i,j) in P} : vry[i,j] = q[i]*v0[i]*sin(theta0[i]) - q[j]*v0[j]*sin(theta0[j]);

s.t. bin11{(i,j) in P} : xr0[i,j]*vry[i,j] - yr0[i,j]*vrx[i,j] <= (1 - z[i,j])*Mbin1[i,j];
s.t. bin12{(i,j) in P} : xr0[i,j]*vry[i,j] - yr0[i,j]*vrx[i,j] >= -z[i,j]*Mbin1[i,j];
s.t. bin311{(i,j) in P : xr0[i,j] >=0 and yr0[i,j] < 0} : 2*a[i,j]*vrx[i,j] - vry[i,j]*(c[i,j] - sqrt(c[i,j]**2 - 4*a[i,j]*b[i,j])) <= (1 - z[i,j])*Mbin311[i,j];
s.t. bin312{(i,j) in P : xr0[i,j] >=0 and yr0[i,j] < 0} : -2*b[i,j]*vry[i,j] + vrx[i,j]*(c[i,j] - sqrt(c[i,j]**2 - 4*a[i,j]*b[i,j])) <= z[i,j]*Mbin312[i,j];
s.t. bin321{(i,j) in P : xr0[i,j] < 0 and yr0[i,j] >=0} : -2*a[i,j]*vrx[i,j] + vry[i,j]*(c[i,j] - sqrt(c[i,j]**2 - 4*a[i,j]*b[i,j])) <= (1 - z[i,j])*Mbin321[i,j];
s.t. bin322{(i,j) in P : xr0[i,j] < 0 and yr0[i,j] >=0} : 2*b[i,j]*vry[i,j] - vrx[i,j]*(c[i,j] - sqrt(c[i,j]**2 - 4*a[i,j]*b[i,j])) <= z[i,j]*Mbin322[i,j];
s.t. bin331{(i,j) in P : xr0[i,j] >=0 and yr0[i,j] >=0} : 2*b[i,j]*vry[i,j] - vrx[i,j]*(c[i,j] + sqrt(c[i,j]**2 - 4*a[i,j]*b[i,j])) <= (1 - z[i,j])*Mbin331[i,j];
s.t. bin332{(i,j) in P : xr0[i,j] >=0 and yr0[i,j] >=0} : 2*a[i,j]*vrx[i,j] - vry[i,j]*(c[i,j] + sqrt(c[i,j]**2 - 4*a[i,j]*b[i,j])) <= z[i,j]*Mbin332[i,j];
s.t. bin341{(i,j) in P : xr0[i,j] < 0 and yr0[i,j] < 0} : -2*b[i,j]*vry[i,j] + vrx[i,j]*(c[i,j] + sqrt(c[i,j]**2 - 4*a[i,j]*b[i,j])) <= (1 - z[i,j])*Mbin341[i,j];
s.t. bin342{(i,j) in P : xr0[i,j] < 0 and yr0[i,j] < 0} : -2*a[i,j]*vrx[i,j] + vry[i,j]*(c[i,j] + sqrt(c[i,j]**2 - 4*a[i,j]*b[i,j])) <= z[i,j]*Mbin342[i,j];
