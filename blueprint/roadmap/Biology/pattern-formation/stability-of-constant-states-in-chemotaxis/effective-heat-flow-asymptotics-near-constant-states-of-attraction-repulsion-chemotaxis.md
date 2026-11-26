# Effective heat-flow asymptotics near constant states of attraction–repulsion chemotaxis

Consider the attraction–repulsion Keller–Segel system on $\mathbb R^n$, $n\ge1$,
$$\partial_t u=\Delta u-\nabla\cdot\big(u\nabla(\beta_1\psi_1-\beta_2\psi_2)\big),\qquad -\Delta\psi_j+\lambda_j\psi_j=u\ (j=1,2),$$
with $u$ the cell density, $\psi_1$ a chemoattractant, $\psi_2$ a chemorepellent, and constants $\beta_j,\lambda_j>0$, $\lambda_1\ne\lambda_2$. Every constant $u\equiv A$ is a steady state. Let $A_*\in(0,\infty]$ be the stability threshold ($A_*=\infty$ if $\beta_1/\beta_2\le\min\{1,\lambda_1/\lambda_2\}$; $A_*=\frac{\lambda_1\lambda_2}{\beta_1\lambda_2-\beta_2\lambda_1}$ if $\beta_1/\beta_2>\lambda_1/\lambda_2$ and $\beta_1/\beta_2\ge(\lambda_1/\lambda_2)^2$; $A_*=\frac{\lambda_1-\lambda_2}{(\sqrt{\beta_1}-\sqrt{\beta_2})^2}$ if $1<\beta_1/\beta_2<(\lambda_1/\lambda_2)^2$), and for $0<A<A_*$ set
$$c_*=1-\frac{\beta_1\lambda_2-\beta_2\lambda_1}{\lambda_1\lambda_2}A>0 .$$

**Theorem.** Let $0<A<A_*$.

1. *Linear level.* For $1\le p\le q\le\infty$ the linearized semigroup satisfies $\|e^{t\mathcal L_A}f-e^{c_*t\Delta}f\|_{L^q}\le Ct^{-\frac n2(\frac1p-\frac1q)}(1+t)^{-1}\|f\|_{L^p}$.
2. *Nonlinear level.* Let $n/2<p\le n$ if $n\ge2$ ($p=1$ if $n=1$) and let $u$ be the global solution from data $u_0=A+v_0$ with $\|v_0\|_{L^p}$ small. Then $\sup_{t>0}t^{\frac n2(\frac1p-\frac1q)}\|u(t)-A\|_{L^q}\le C\|u_0-A\|_{L^p}$ for all $p\le q\le\infty$. If $n\ge2$ and $n/2<p<n$,
$$t^{\frac n2(\frac1p-\frac1q)}\big\|u(t)-A-e^{c_*t\Delta}(u_0-A)\big\|_{L^q}\le C\big(t^{-1}+t^{-\frac n2(\frac1p-\frac1n)}\big)\|u_0-A\|_{L^p},$$
and in the critical case $p=n$ with $\|u_0-A\|_{L^n}$ small enough the same normalized difference tends to $0$ as $t\to\infty$.

So near a stable constant density the cells spread as a pure heat flow with effective diffusivity $c_*$, reduced below one by the net attraction $\beta_1/\lambda_1-\beta_2/\lambda_2$ times $A$.

## Expansion

Linearizing at $A$ gives the Fourier symbol $-|\xi|^2\big(1-A\frac{\beta_1}{|\xi|^2+\lambda_1}+A\frac{\beta_2}{|\xi|^2+\lambda_2}\big)$. At $\xi=0$ the bracket equals $c_*$, and $A<A_*$ keeps the bracket positive for all $\xi$, so the linearized operator is dissipative. Expanding the symbol at low frequency, $-c_*|\xi|^2+O(|\xi|^4)$, the correction contributes one extra power of $t^{-1}$ after the usual $L^p$–$L^q$ smoothing, giving the linear estimate. The nonlinear term $\nabla\cdot(v\nabla K*v)$ is quadratic in the perturbation $v=u-A$ and, by Duhamel and the decay estimates, decays faster than the linear part, at the extra rate $t^{-\frac n2(\frac1p-\frac1n)}$. Combining the two steps yields the effective heat-flow profile; if also $u_0-A\in L^1$, the leading term is a Gaussian $G(c_*t)\int(u_0-A)$.

## Sources

- H. Wakui, T. Yamada, *Large-time behavior in an attraction--repulsion chemotaxis system* (2026), Theorems 1.1, 1.2 and 1.3 (building on the stability result recalled as Proposition 1.1). <https://doi.org/10.48550/arXiv.2609.18258>
