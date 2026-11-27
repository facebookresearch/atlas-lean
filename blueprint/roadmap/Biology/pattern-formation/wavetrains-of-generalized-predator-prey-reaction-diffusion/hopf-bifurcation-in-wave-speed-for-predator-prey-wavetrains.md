# Hopf bifurcation in the wave speed for wavetrains of generalized predator–prey reaction–diffusion systems

**Model.** Prey $N(x,t)$ and predators $P(x,t)$ diffuse with coefficients $D_1,D_2>0$ and react according to

$$N_t=D_1N_{xx}+NF(N)-\alpha NP-\frac{\epsilon N^2}{k},\qquad P_t=D_2P_{xx}-PG(P)+\beta NP,$$

with general smooth prey growth $F$ and predator death $G$, predation rate $\alpha$, conversion rate $\beta$, prey crowding $\epsilon$ and carrying capacity $k$. Travelling waves $N(x-vt)$, $P(x-vt)$ satisfy the four-dimensional "spatial" system in $\zeta=x-vt$

$$N'=M,\quad M'=\frac1{D_1}\Bigl(-vM-NF(N)+\alpha NP+\frac{\epsilon N^2}{k}\Bigr),\quad P'=Q,\quad Q'=\frac1{D_2}\bigl(-vQ+PG(P)-\beta NP\bigr),$$

with coexistence fixed point $(N_0,0,P_0,0)$, $N_0=G(P_0)/\beta$, $P_0=\bigl(F(N_0)-\epsilon N_0/k\bigr)/\alpha$. Write $F_0=F(N_0)$, $G_0=G(P_0)$, $F_0'=F'(N_0)$, $G_0'=G'(P_0)$.

**Theorem.** The last Routh–Hurwitz condition for the fixed point, at equality, is the quartic $f(v)=v^2(Av^2+B)=0$ with explicit coefficients $A,B$ depending on $D_1,D_2,\alpha,\beta,\epsilon,k,F_0,F_0',G_0,G_0'$; in particular

$$A=\frac{(D_1+D_2)\bigl(-\epsilon\alpha G_0+\alpha kF_0'G_0+(\epsilon G_0-\beta kF_0)G_0'\bigr)}{\alpha\beta k\,D_1^3D_2^3}.$$

If $AB<0$, there are two critical wave speeds $v_\mp=\mp\sqrt{-B/A}$. If $A>0>B$ the fixed point is stable for $|v|>v_+$ and unstable for $|v|<v_+$; if $A<0<B$ the reverse holds; if $A\ge0$, $B>0$ it is stable for all $v$, and if $A\le0$, $B<0$ unstable for all $v$. At $v=v_\mp$ the characteristic polynomial factors as $(\lambda^2+\omega^2)(\lambda^2+s\lambda+p)$ with

$$\omega^2=\frac{G_0'(\epsilon G_0-\beta kF_0)+\alpha G_0(kF_0'-\epsilon)}{\alpha\beta k(D_1+D_2)},$$

and, with bifurcation parameter $\mu=1/v-1/v_0$, the transversality condition $\frac{d}{d\mu}\operatorname{Re}\lambda\big|_{\mu=0}>0$ holds (given $D_1+D_2>0$ and $\omega^2>0$). Hence a Hopf bifurcation of the spatial ODE occurs at each of the two wave speeds $v_\mp$, producing periodic orbits in $\zeta$, i.e. periodic wavetrains of the PDE.

For five specific choices of the nonlinearities (systems A–E), supercritical bifurcations give stable periodic wavetrains, while subcritical ones can give spatially coherent wavetrains with chaotic temporal dynamics when the subcritical bifurcation ends the stability regime.

## Depends on

- [Fisher–KPP travelling waves](../fisher-kpp-travelling-waves/README.md)
- [Lotka–Volterra predator–prey model](../../population-dynamics/lotka-volterra-predator-prey-model/README.md)

## Expansion

The Jacobian of the spatial system at the coexistence point gives a quartic characteristic polynomial $\lambda^4+b_1\lambda^3+b_2\lambda^2+b_3\lambda+b_4$ with $b_1=(D_1+D_2)v/(D_1D_2)$ and $b_2,b_3,b_4$ depending on $v$ through $v^2$ and $v$. A purely imaginary pair exists exactly when the Hurwitz determinant $b_1b_2b_3-b_3^2-b_1^2b_4$ vanishes, which reduces to $v^2(Av^2+B)=0$. At $v=v_\mp$ one has $b_4=b_2b_3/b_1-b_3^2/b_1^2$, giving the factorization with $\omega^2=b_3/b_1$; the discriminant of the quartic is then negative, confirming one imaginary pair and two real roots. Implicit differentiation of $g(\lambda(v),v)=0$ at $\lambda=i\omega$ yields $\frac{d\operatorname{Re}\lambda}{dv}=\omega^2\Psi/(\cdots)$ with $\Psi$ proportional to $-\omega^2(D_1+D_2)$, so $\operatorname{Re}\lambda$ decreases in $v$; since $dv/d\mu<0$, the eigenvalues cross the imaginary axis with positive speed in $\mu$, and the Hopf theorem applies.

## Sources

- Stefan C. Mancas, Roy S. Choudhury, "Periodic and Chaotic Traveling Wave Patterns in Reaction-Diffusion/Predator-Prey Models with General Nonlinearities", arXiv (2013). Section 1 (model and travelling-wave system), Section 2 (linear stability, quartic Hopf curve and cases (a)–(d)), Section 3 (Lemma 1, Theorem 1 and the transversality computation), Sections 4–5 (systems A–E and numerical results). <https://doi.org/10.48550/arXiv.1302.2499>. Published version: Far East Journal of Dynamical Systems 11(2) (2009), 117–142, <https://doi.org/10.17654/0972111809010>; locators above refer to the arXiv version.
