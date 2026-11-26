# Coefficient-sign criterion for Turing-like instability with conservation laws

**Setting.** Consider a mass-action reaction network with $n$ species, stoichiometric matrix $\Gamma$ of rank $s<n$ (so $n-s$ conserved totals), ODE $\dot c=\Gamma r(k,c)$ and reaction-diffusion system $\partial_t c=\Gamma r(k,c)+D\Delta c$ on a bounded domain $\Omega\subset\mathbb{R}^d$, $d\in\{1,2,3\}$, with Neumann boundary conditions and $D=\operatorname{diag}(d_1,\dots,d_n)$, $d_i>0$. Let $\bar c>0$ be a steady state, $J=J(\bar c)$ the Jacobian (rank $s$), and $A(\mu)=J-\mu D$. The homogeneous state is linearly unstable in the PDE if some $A_\ell=J-\mu_\ell D$ has an eigenvalue with positive real part, where $0=\mu_0<\mu_1\le\mu_2\le\cdots$ are the Neumann eigenvalues of $-\Delta$ on $\Omega$.

**Determinant structure (Lemma 3.1).** $\det A(\mu)=\det D\cdot\det(JD^{-1}-\mu I_n)$, i.e. up to the positive constant $\det D$ it is the characteristic polynomial of $JD^{-1}$; it is not identically zero, and with the $n-s$ conservation laws
$$\det A(\mu)=\det D\;\mu^{n-s}\big(a_0\mu^s+a_1\mu^{s-1}+\cdots+a_{s-1}\mu+a_s\big).$$
If $\operatorname{sign}\det A(\mu)=(-1)^{n+1}$ then $A(\mu)$ has an odd number (at least one) of positive real eigenvalues (Corollary 3.3).

**Theorem 3.4.** Suppose
$$\operatorname{sign}(a_0)=(-1)^n,\qquad \operatorname{sign}(a_s)=(-1)^{n+1},$$
and let $\bar\mu>0$ be the smallest positive root of $\det A(\mu)=0$. If $\Omega$ is simply connected and
- $d=1$ (interval): $|\Omega|>\pi/\sqrt{\bar\mu}$;
- $d=2$: $|\Omega|>p_{1,1}^2\,\pi/\bar\mu$, with $p_{1,1}\approx1.8412$ the first positive zero of $J_1'$;
- $d=3$: $|\Omega|>\tfrac{4}{3}p_{3/2,1}^3\,\pi/\bar\mu^{3/2}$, with $p_{3/2,1}\approx2.0816$ the first positive zero of $\big(x^{-1/2}J_{3/2}(x)\big)'$;

then some Neumann eigenvalue $\mu_\ell$ gives a matrix $A_\ell$ with an odd number (at least one) of positive eigenvalues. If $\bar\mu$ is the only positive root, these size conditions are also necessary (Corollary 3.5).

**Corollary 3.6.** If in addition all nonzero eigenvalues of $J(\bar c)$ have negative real part (the steady state is stable in the ODE within its compatibility class), a Turing-like instability occurs.

When the positive steady states have a monomial parameterization $\bar c=\psi(k)\circ\xi^{A}$, the coefficients $a_0,a_s$ are rational functions of rate constants, diffusion coefficients and the free parameters $\xi$, so the conditions become polynomial inequalities.

## Depends on

- [Determinant of the mode matrix is the dispersion polynomial](../turing-patterns-and-diffusion-driven-instability/det-mode-matrix.md)
- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

The determinant of a real matrix is the product of its eigenvalues; complex ones come in conjugate pairs with positive product, so $\operatorname{sign}\det A=(-1)^{n}$ times $(-1)^{\#\{\text{positive real eigenvalues}\}}$ whenever no eigenvalue vanishes. Opposite signs of $a_0$ and $a_s$ force a sign change of the bracket on $(0,\infty)$; on $(0,\bar\mu)$ the sign equals that of $a_s$, namely $(-1)^{n+1}$, so every $A(\mu)$ with $0<\mu<\bar\mu$ has a positive eigenvalue. It remains to ensure $\mu_1<\bar\mu$: on an interval $\mu_1=(\pi/|\Omega|)^2$, and in two and three dimensions the Szegő-Weinberger inequality bounds $\mu_1$ by the first nonzero Neumann eigenvalue of the disc or ball of the same measure, which gives the stated thresholds. The conservation laws contribute the factor $\mu^{n-s}$, which is why the classical trace-determinant conditions for two species do not apply directly.

## Sources

- Carsten Conradi, Maya Mincheva, Hannes Uecker, "Conditions for spatial instabilities and pattern formation from monomial steady state parameterizations", arXiv:2605.16049 (2026), Lemma 3.1, Corollaries 3.2-3.3, Theorem 3.4, Corollaries 3.5-3.6 (Section 3), <https://doi.org/10.48550/arXiv.2605.16049>
