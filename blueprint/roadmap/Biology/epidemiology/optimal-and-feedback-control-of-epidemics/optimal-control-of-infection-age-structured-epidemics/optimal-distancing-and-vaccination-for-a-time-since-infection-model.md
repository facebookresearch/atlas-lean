# Optimal distancing and vaccination for an epidemic structured by time since infection

**State system.** Let $s(t)$ be the susceptible fraction and $Y(x,t)$ the density of infected individuals with time since infection $x\in[0,x_+]$. With infectivity $\beta_0(x)\ge0$, removal hazard $\gamma(x)$ with survival $\Gamma(x)=e^{-\int_0^x\gamma}$ ($\Gamma(x_+)=0$), demographic turnover $\delta$, a contact-reduction control $c(t)$ and a vaccination rate $v(t)$ (successful immunizations per head),

$$s'(t)=-v(t)+\delta(1-s(t)),\qquad (\partial_t+\partial_x)Y=-\gamma(x)Y,\qquad Y(0,t)=c(t)s(t)\int_0^{x_+}\beta_0(x)Y(x,t)\,dx,$$

with $s(0)=1$, $Y(x,0)=Y_0(x)$. Along characteristics, the force of infection $Z(t)=\int_0^{x_+}\beta_0(x)Y(x,t)\,dx$ solves the Volterra equation

$$Z(t)=\int_0^t c(\sigma)s(\sigma)\,\beta_0(t-\sigma)\Gamma(t-\sigma)\,Z(\sigma)\,d\sigma+F(t),\qquad F(t)=\int_0^\infty\beta_0(x+t)\Gamma(x+t)\frac{Y_0(x)}{\Gamma(x)}\,dx,$$

and $s(t)=1-\int_0^te^{-\delta(t-\sigma)}v(\sigma)\,d\sigma\ge e^{-\delta t}$ when $v\le\delta$. The uncontrolled reproduction number is $\mathcal R_0^0=c_0\int_0^{x_+}\beta_0\Gamma$.

**Control problem.** Admissible controls $\mathcal U$: $c_-\le c(t)\le c_0$ on $[0,T]$; $v=0$ before vaccine arrival $T_1$ and $0\le v\le\delta$ on $[T_1,T]$. Minimize

$$\Phi(c,v)=A_0\int_0^Tc\,s\,Z\,dt+A_1\int_0^TQ(c)\,dt+\int_0^T\Bigl(A_{21}v+\frac{A_{22}}2v^2\Bigr)dt ,$$

new infections plus the social cost $Q$ of distancing (decreasing, vanishing at $c_0$) plus vaccination cost.

**Theorem.** Assume $\beta_0\in W^{1,\infty}$, $\gamma\Gamma\in L^\infty$, $\int_0^{x_+}\gamma=\infty$, $Y_0/\Gamma\in L^\infty$, $c_->0$, and $Q$ of class $C^1$ and strictly convex on $[c_-,c_0]$ (the source's (34)).

1. For every $(c,v)\in\mathcal U$ the state system has a unique solution, with $Z\in W^{1,\infty}(0,T)$, $0\le Z\le M=\|\beta_0\|_\infty\|Y_0\|e^{c_0\|\beta_0\|_\infty T}$ and $Z$ Lipschitz with an explicit constant.
2. An optimal pair $(c^*,v^*)$ exists.
3. *(First-order conditions.)* With $(p,q)$ the solution of the backward adjoint (dual) system, $E_1=-q\,s^*Z^*$ and $E_2=p-A_{21}$,

$$c^*(t)=\mathcal L[f_1,c_-,c_0]\big(E_1(t)\big),\qquad v^*(t)=0\ \text{on }[0,T_1],\qquad v^*(t)=\mathcal L[f_2,0,\delta]\big(E_2(t)\big)\ \text{on }[T_1,T],$$

where for strictly increasing $f$ on $[a,b]$, $\mathcal L[f,a,b]$ is the pointwise inverse of $f$ plus the normal cone of the box $[a,b]$ (the clipped inverse of $f$), $f_1(c)=A_1Q'(c)$ and $f_2(v)=A_{22}v$.

## Expansion

The PDE reduces to a renewal (Lotka–McKendrick) equation: newly infected at time $t-x$ survive to class age $x$ with probability $\Gamma(x)$, so $Y(x,t)=c(t-x)s(t-x)Z(t-x)\Gamma(x)$ for $x\le t$. Existence for the Volterra equation follows from Picard iterates with a bounded kernel, with continuous dependence on kernel and forcing; a minimizing sequence has weak-$*$ convergent controls, the states converge strongly, and convexity of $Q$ and of the vaccination cost gives lower semicontinuity. Needle-free convex variations of the controls give the variational system, and the box-constrained variational inequalities are solved pointwise by the clipped inverse $\mathcal L$, yielding bang-bang/interior switching between full distancing $c_-$ and normal contacts $c_0$.

## Sources

- Alberto d’Onofrio, Mimmo Iannelli, Piero Manfredi, Gabriela Marinoschi, "Optimal Epidemic Control by Social Distancing and Vaccination of an Infection Structured by Time Since Infection: The COVID-19 Case Study", SIAM Journal on Applied Mathematics 84 (2024), S199–S224, <https://doi.org/10.1137/22m1499406>. Published version of arXiv:2405.06628, cited next; locators there refer to the arXiv version.
- A. d'Onofrio, M. Iannelli, P. Manfredi, G. Marinoschi, "Optimal epidemic control by social distancing and vaccination of an infection structured by time since infection: the covid-19 case study", arXiv:2405.06628 (2024), Section 2 (state system and assumptions, multi-period setting), Section 3 (Volterra existence theorem, a priori bound proposition, existence of an optimal control) and Section 4 (system in variations, dual system, normal-cone lemma and first-order optimality theorem). <https://doi.org/10.48550/arXiv.2405.06628>
