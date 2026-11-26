# Integral representation of the bistable zero-speed threshold

Consider the Lotka–Volterra competition–diffusion system
$$
u_t=u_{xx}+u(1-u-av),\qquad v_t=d\,v_{xx}+r\,v(1-v-bu),\qquad x\in\mathbb{R},
$$
under **strong competition** $a>1$, $b>1$, $d,r>0$. Both $(1,0)$ and $(0,1)$ are stable for the kinetics. There is a unique monotone front $(u,v)=(U,V)(x+ct)$ with $(U,V)(-\infty)=(0,1)$, $(U,V)(+\infty)=(1,0)$, $U'>0>V'$, and its speed $c=c(d,r,a,b)$ is unique, continuous, strictly decreasing in $a$ and strictly increasing in $b$. For fixed $a,d,r$ there is a unique **zero-speed threshold** $b_*(a,d,r)>1$:
$$
c<0\iff 1<b<b_*,\qquad c=0\iff b=b_*,\qquad c>0\iff b>b_*,
$$
so that $u$ invades $v$ exactly when $b>b_*$. A standing front depends on $d,r$ only through $\rho=d/r$, and $\sqrt a<b_*(a,d,r)<a^2$.

**Gaussian splitting recursion.** Fix $a>1$ and $\rho=d/r$, let $s(x)=1/(1+e^{-x})$, $G_{\kappa,h}(x)=(4\pi\kappa h)^{-1/2}e^{-x^2/(4\kappa h)}$, and for $m\ge1$ set $N_m=\lceil(1+a^2)m^2e^{m^2}\rceil$, $h_m=m/N_m$. For $\beta\in[\sqrt a,a^2]$ start from $p_0=q_0=s$ and iterate, for $0\le k<N_m$,
$$
p_{k+1}=G_{1,h_m}*\bigl[p_k+h_m\,p_k(1-a-p_k+aq_k)\bigr],\qquad
q_{k+1}=G_{\rho,h_m}*\bigl[q_k+h_m(1-q_k)(\beta p_k-q_k)\bigr].
$$
(This is a time-$h_m$ Euler step for the reaction followed by an exact heat step, applied to the cooperative variables $(p,q)=(u,1-v)$ with $(d,r,b)=(\rho,1,\beta)$.) Define the **excess mass**
$$
M_m(a,\rho,\beta)=\int_{\mathbb{R}}\bigl[p_{N_m}(x)-s(x)\bigr]\,dx .
$$

**Theorem.** For every $m\ge1$ and $\beta\in[\sqrt a,a^2]$ the iterates take values in $[0,1]$, and $M_m$ is absolutely convergent and equal to $h_m\sum_{k<N_m}\int p_k(1-a-p_k+aq_k)\,dx$. Moreover
$$
b_*(a,d,r)=\sqrt a+\lim_{m\to\infty}\int_{\sqrt a}^{a^2}\frac{d\beta}{1+\exp\bigl(M_m(a,d/r,\beta)\bigr)} .
$$

**Lemma (excess mass measures the speed).** Let $(p,q)$ be the exact cooperative solution with data $(s,s)$ and $J(t)=\int_{\mathbb{R}}[p(t,x)-s(x)]\,dx$. Then $J(t)/t\to c(\rho,1,a,\beta)$ as $t\to\infty$.

## Expansion

Since $s(-x)=1-s(x)$, a step function translated by $ct$ has excess mass exactly $ct$ relative to $s$. Front comparison and exponential tail bounds show that the solution stays within a bounded distance of such a step, which gives the lemma without needing convergence to the wave in $L^1$. An $L^1$ splitting estimate $\|Z_N-z(T)\|_{L^1}\le C(a,\rho)\,Th\,e^{2(2a^2+1)T}$, uniform in $\beta$, together with the choice $T=m$, $h=h_m$, gives $M_m/m\to c(\rho,1,a,\beta)$. The logistic factor $1/(1+e^{M_m})$ therefore tends to $1$ where $c<0$ (that is, $\beta<b_*$) and to $0$ where $c>0$, and dominated convergence on $[\sqrt a,a^2]$ returns $b_*-\sqrt a$. The formula uses no unknown wave profile or speed function; it gives no rate of convergence for the threshold itself.

## Sources

- S. Ma, D. Xiao, M. Zhou, "Sharp Thresholds for Linear Determinacy and Zero Wave Speed in Lotka-Volterra Competition-Diffusion Systems", arXiv preprint (2026), Theorem 1.1, Section 2 (Lemma 2.4) and Sections 3–5, <https://doi.org/10.48550/arXiv.2610.16748>.
