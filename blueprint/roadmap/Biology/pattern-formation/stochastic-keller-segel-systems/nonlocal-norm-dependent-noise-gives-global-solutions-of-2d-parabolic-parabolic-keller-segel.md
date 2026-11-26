# Nonlocal norm-dependent noise gives global solutions of the 2D parabolic–parabolic Keller–Segel system

Let $\mathcal{O} \subset \mathbb{R}^2$ be a bounded domain with smooth boundary and outward normal $\nu$. Consider the fully parabolic Keller–Segel system with noise acting only on the cell density $u$,

$$
\begin{cases}
du = \big(\Delta u - \nabla\cdot(u \nabla v)\big)\,dt + \sigma(u)\,dW(t), & x \in \mathcal{O},\ t > 0,\\
dv = (\Delta v - v + u)\,dt, & x \in \mathcal{O},\ t > 0,\\
\partial_\nu u = \partial_\nu v = 0 & \text{on } \partial\mathcal{O},
\end{cases}
$$

where $W = \sum_k e_k W_k$ is a cylindrical Wiener process on a separable Hilbert space $U$ with orthonormal basis $(e_k)$, and the noise coefficient is **nonlocal and nonlinear**:

$$
(\sigma(u) e_k)(x) = b_k\, \|u\|_{L^p(\mathcal{O})}^{\,r}\, u(x), \qquad 2 < p < \infty, \quad 1 < r < \frac{p}{p-2}, \quad (b_k) \in \ell^2,
$$

with $B_0^2 = \sum_k b_k^2 > 0$. The noise intensity at a point depends on the global $L^p$ size of the population, modeling common environmental fluctuations felt by all cells.

**Theorem.** For every $u_0 \in L^2(\mathcal{O})$ and $v_0 \in W^{1,\infty}(\mathcal{O})$ there is a global, pathwise unique strong solution: an adapted process $u$ with continuous paths in $L^2(\mathcal{O})$ such that, for every $T > 0$, $u \in L^2(\Omega; C([0,T]; L^2(\mathcal{O}))) \cap L^2(\Omega; L^2(0,T; H^1(\mathcal{O})))$ and the maximal existence time $\tau^*$ equals $+\infty$ almost surely. No smallness of the initial mass is required.

This contrasts with the deterministic system on a bounded planar domain, where global existence versus blow-up is governed by the critical mass $4\pi$ of $\int_{\mathcal{O}} u_0$.

## Expansion

The drift and the noise are neither coercive nor globally Lipschitz, and $v$ must be controlled through its own parabolic equation, for which maximal-regularity bounds give $\int_0^t \|\nabla v\|_{L^\infty}^2\,ds$ in terms of $\|\nabla v_0\|_{L^\infty}$ and $\int_0^t \|u\|_{H^1}^2\,ds$. One first solves a truncated system, in which chemotaxis and noise are multiplied by a cutoff $\theta_N(\|u\|_{X_t}^2)$, by Banach's fixed point theorem; pathwise uniqueness then patches the truncated solutions into a unique maximal solution $(u, \tau^*)$. Globality comes from applying Itô's formula to the concave functional $(1 + \|u\|_{L^2}^2)^\alpha$ with $\alpha \in (\max\{0, (2-r)/2\}, 1/2)$: the Itô correction from the noise, proportional to $-\alpha(1-\alpha) B_0^2 \|u\|_{L^p}^{2r} \|u\|_{L^2}^4 (1+\|u\|_{L^2}^2)^{\alpha-2}$, absorbs the chemotactic growth, giving the bound

$$
\mathbb{E}\sup_{0 \le t \le T}\big(1 + \|u(t \wedge \tau_N)\|_{L^2}^2\big)^\alpha + \mathbb{E}\int_0^{T \wedge \tau_N} \frac{\|\nabla u\|_{L^2}^2}{(1 + \|u\|_{L^2}^2)^{1-\alpha}}\,ds \le C(T)
$$

uniformly in $N$, which rules out $\tau^* < \infty$.

## Sources

- J. Wang, Q. Li and H. Huang, *Global existence and pathwise uniqueness for a stochastic parabolic-parabolic Keller-Segel system*, arXiv:2607.24128 (2026), Section 2 (Assumption 1, Definitions 1–2), Theorem 1; Section 3, Theorems 2–5. <https://doi.org/10.48550/arXiv.2607.24128>
