restart; with(linalg):
`expandmatrix`:=proc(B::matrix)
    local i,j;
    with(grobner,normalf); with(Groebner,spoly); 
    with(linalg,multiply);
    for i from 1 to 3 do 
        for j from 1 to 3 do 
            B[i,j]:=expand(B[i,j]);
        od;
    od;
    RETURN(B);
;end:

`expandvector`:=proc(V::matrix)
    local i,j;
    with(grobner,normalf); with(Groebner,spoly); 
    with(linalg,multiply); 
    for i from 1 to 3 do 
        V[i,1]:=expand(V[i,1]);
    od;
    RETURN(V);
;end:

Unimod:=proc(f,X::name)
    local n,a,b,S,alfa,s,t,d,i,j,u;
    n:=nops(f);
    a[1]:=f[1];
    b[1]:=f[2];
    for i from 1 to n-2 do
        d[i]:=gcdex(a[i],b[i],X,'s[i]','t[i]');
        a[i+1]:=a[i]*s[i]+b[i]*t[i];b[i+1]:=f[i+2];
    od;
    d[n-1]:=gcdex(a[n-1],b[n-1],X,'s[n-1]','t[n-1]');
    u[1]:=product(s[j],j=1..n-1);u[n]:=t[n-1];
    for i from 2 to n-1 do
        u[i]:=(product(s[j],j=i..n-1))*t[i-1]
    od;
    d[n-1];
    [seq(sort(u[j],x),j=1..n)];
end proc:

for i from 1 to 3 do
    nprintf("donner le composant numéro %d du vecteur :",i);
    V[i,1]:=readstat();
od;

V:=matrix(3,1,[V[1,1],V[2,1],V[3,1]]):
V1:=V[1,1]:V2:=V[2,1]:V3:=V[3,1]:
with(Groebner):
WL:=[V1,V2,V3]:
GB:=gbasis(WL,plex(x,y)):
L:=degree(V1,x)+1:

for i from 1 to L do 
    y[i]:=i-1; 
    w[i]:=expand(V2+y[i]*V3);
    r[i]:=expand(resultant(V1,w[i],x));
    gcdex(V1,w[i],r[i],x,'s','t'): f[i]:=s; g[i]:=t;
od:

R0:=Vector[row](L):
for i from 1 to L do
    R0[i]:=r[i];
od:

R:=convert(R0,'list'):
A:=Unimod(R,y):
for i from 1 to nops(R) do 
    alfa[i]:=expand(op(i,A));
od:

b[L]:=0:
for i from 1 to L do 
    b[L-i]:=expand(b[L-i+1]+alfa[L-i+1]*r[L-i+1]*x);
    gama[i]:=matrix(3,3,[1,0,0,0,1,y[i],0,0,1]);
od:

for i from 1 to L+1 do 
    v[3,i-1]:=expand(subs(x=b[i-1],V3));
od:

for i from 1 to L do 
    alfar[i]:=expand(alfa[i]*r[i]*x);
    F[i,3]:=expand((v[3,i-1]-v[3,i])/(alfar[i]));
od:

for i from 1 to L do
    sigma[i,3]:=expand(alfa[i]*x*F[i,3]*subs(x=b[i-1],f[i]));
    beta[i,3]:=expand(alfa[i]*x*F[i,3]*subs(x=b[i-1],g[i]));
    E[3,1,i]:=matrix(3,3,[1,0,0,0,1,0,-sigma[i,3],0,1]);
    E[3,2,i]:=matrix(3,3,[1,0,0,0,1,0,0,-beta[i,3],1]);
    Gamma[i]:=matrix(multiply(E[3,1,i],E[3,2,i]));
    gamab[i]:=subs(y=b[i-1],gama[i]);
od:

with(linalg,multiply):
for i from 1 to L do
    B[i,2]:=expandmatrix(multiply(Gamma[i],gama[i]));
    s[i,1]:=expand((subs(x=x+Y*z,V1)-V1)/Y); 
    s[i,2]:=expand((subs(x=x+Y*z,w[i])-w[i])/Y);
    t[i,1]:=expand((subs(x=x+Y*z,f[i])-f[i])/Y); 
    t[i,2]:=expand((subs(x=x+Y*z,g[i])-g[i])/Y);
    sc[i,1]:=subs(x=b[i-1],y=r[i],z=-alfa[i]*x,s[i,1]);
    tc[i,2]:=expand(subs(x=b[i-1],y=r[i],z=-alfa[i]*x,t[i,2]));
    c[i,1,1]:=1+expand(sc[i,1]*subs(x=b[i-1],f[i])+tc[i,2]*subs(x=b[i-1],w[i]));
    c[i,1,2]:=expand(sc[i,1]*subs(x=b[i-1],g[i])-tc[i,2]*subs(x=b[i-1],V1));
    sc[i,2]:=expand(subs(x=b[i-1],Y=r[i],z=-alfa[i]*x,s[i,2]));
    tc[i,1]:=expand(subs(x=b[i-1],Y=r[i],z=-alfa[i]*x,t[i,1]));
    c[i,2,1]:=expand(sc[i,2]*subs(x=b[i-1],f[i])-tc[i,1]*subs(x=b[i-1],w[i]));
    c[i,2,2]:=1+expand(sc[i,2]*subs(x=b[i-1],g[i])+tc[i,1]*subs(x=b[i-1],V1));
    C[i]:=matrix(3,3,[c[i,1,1],c[i,1,2],0,c[i,2,1],c[i,2,2],0,0,0,1]);
    gama2[i]:=inverse(gama[i]);
    B[i,1]:=expandmatrix(multiply(subs(x=b[i],gama2[i]),C[i]));
    B[i]:=expandmatrix(multiply(B[i,1],B[i,2]));
od:

with(linalg,multiply): 
B:=expandmatrix(multiply(B[2],B[1]));
print(`On multiplie B et V, si on trouve V(0,y) c'est correct, et c'est le cas`);
BV:=expandvector(multiply(B,V));