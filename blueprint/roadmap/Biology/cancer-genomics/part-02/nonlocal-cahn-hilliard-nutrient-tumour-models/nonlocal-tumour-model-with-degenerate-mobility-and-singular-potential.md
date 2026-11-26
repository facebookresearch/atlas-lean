# Nonlocal tumour model with degenerate mobility and singular potential

Consider the nonlocal Cahn–Hilliard–nutrient tumour model of the article below, now with a cell mobility $m:[-1,1]\to[0,\infty)$ that vanishes at the pure phases $\varphi=\pm1$ and a singular potential $\Psi$ defined on $(-1,1)$ (for example the logarithmic potential $\Psi(s)=\frac\theta2\big((1+s)\log(1+s)+(1-s)\log(1-s)\big)-\frac{\theta_c}{2}s^2$ with $0<\theta<\theta_c$ and $m(s)=1-s^2$). Let $M$ be the entropy of the mobility, $m(s)M''(s)=1$, $M(0)=M'(0)=0$.

**Assumptions.** $\Psi=\Psi_1+\Psi_2$ with $\Psi_2\in C^2([-1,1])$ and singular part $\Psi_1\in C^2(-1,1)$ whose second derivative is monotone near $\pm1$; $A\Psi''+Ba\ge c_0>\chi^2$ on $(-1,1)$; $m$ continuous, $m(s)=0$ iff $s=\pm1$, $m\Psi''\in C([-1,1])$ and $m$ monotone near $\pm1$; $P$ continuous, nonnegative, with $\sqrt{P}\le c_7m$ near $\pm1$ and $P\Psi'\in C([-1,1])$; the nutrient mobility $n$ and the kernel $J$ satisfy the non-degenerate hypotheses; $|\varphi_0|\le1$, $M(\varphi_0)\in L^1$ and $\sigma_0\in L^2$.

**Existence.** Under these assumptions there is a weak solution $(\varphi,\sigma)$ with $\varphi,\sigma\in L^\infty(0,T;L^2)\cap L^2(0,T;H^1)\cap H^1(0,T;(H^1)')$ and $|\varphi|\le1$ a.e. in $\Omega\times(0,T)$, formulated without the chemical potential:

$$
\langle\varphi_t,\zeta\rangle+\big(m(\varphi)(A\Psi''(\varphi)+Ba)\nabla\varphi,\nabla\zeta\big)+\big(m(\varphi)(B\varphi\nabla a-B\nabla(J\star\varphi)-\chi\nabla\sigma),\nabla\zeta\big)=\big(P(\varphi)\,R,\zeta\big),
$$

$$
\langle\sigma_t,\zeta\rangle+\big(n(\varphi)\nabla(\sigma+\chi(1-\varphi)),\nabla\zeta\big)=-\big(P(\varphi)\,R,\zeta\big),
$$

for all $\zeta\in H^1(\Omega)$, where $R=(1+\chi)\sigma+\chi(1-\varphi)-A\Psi'(\varphi)-Ba\varphi+BJ\star\varphi$, and the initial data are attained in $L^2$.

**Continuous dependence.** If moreover $n=1$, $m$ is Lipschitz, $\chi=0$, $\rho\Psi_1''+\Psi_2''+a\ge0$ for some $\rho\in[0,1)$, $m\Psi_1''\ge c_8>0$, and $P,P\Psi'$ are Lipschitz on $[-1,1]$, then two such solutions satisfy the same $(H^1)'$–$L^2$ stability estimate as in the non-degenerate case; in particular the solution is unique.

## Expansion

Degeneracy of $m$ at $\pm1$ switches off Cahn–Hilliard diffusion in the pure phases, and the singular potential keeps $\varphi$ in the physical range; together they prevent the unphysical overshoot $|\varphi|>1$ that regular potentials allow. Because $\nabla\mu$ is no longer controlled when $m$ degenerates, $\mu$ is eliminated using $m\Psi''\in C([-1,1])$, following the Elliott–Garcke approach. Solutions are obtained as limits of problems with a positive mobility and regularised potential, using the entropy estimate from testing with $M'(\varphi)$ to force $|\varphi|\le1$ in the limit; the condition $\sqrt P\le c_7m$ near $\pm1$ makes the source vanish there. The stability result excludes chemotaxis because the available regularity of $\sigma$ cannot control the term $m(\varphi)\chi\nabla\sigma$ in the difference equation.

## Depends on

- [Weak solutions of the nonlocal Cahn–Hilliard–nutrient tumour model](weak-solutions-of-the-nonlocal-cahn-hilliard-nutrient-tumour-model.md)

## Sources

- S. Frigeri, K. F. Lam, E. Rocca, "On a diffuse interface model for tumour growth with non-local interactions and degenerate mobilities", Section 2 (Theorems 2.3 and 2.4) and Section 4. <https://doi.org/10.48550/arXiv.1703.03553>
