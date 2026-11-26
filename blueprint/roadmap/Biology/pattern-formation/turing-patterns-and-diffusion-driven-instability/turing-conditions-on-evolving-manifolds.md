# Turing instability conditions on an evolving manifold

This page covers Theorem 3.3 of Van Gorder, Klika and Krause (2021), which generalises the Turing condition from a static domain to a smoothly evolving one.

**Setting.** Let $\Omega(t) \subset \mathbb{R}^N$ be a compact, simply connected, smooth Riemannian manifold that evolves by coordinate-wise dilation, $X = (r_1(t)\chi_1(x), \dots, r_N(t)\chi_N(x))$ for $x$ in the initial manifold, so that local volume change depends on time only. A two-species system $u = (u_1, u_2)$ obeys conservation with advection by the domain velocity $Q$,
$$\partial_t u + \nabla_{\Omega(t)} \cdot (Q u) = D\, \nabla^2_{\Omega(t)} u + f(u), \qquad D = \mathrm{diag}(d_1, d_2),$$
with no-flux boundary conditions if $\partial\Omega(t) \neq \emptyset$. Write $\dot\mu/\mu = \partial_t \log |\det G|^{1/2}$ for the dilution rate ($G$ the metric tensor), and let $0 = \rho_0(t) < \rho_1(t) \le \rho_2(t) \le \cdots$ be the Laplace-Beltrami eigenvalues, $\nabla^2_{\Omega(t)} \Psi_k = -\rho_k \Psi_k$ (for isotropic growth $r_j = r$, $\rho_k(t) = \rho_k(0)/r(t)^2$).

The spatially uniform base state solves the diluted kinetics
$$\dot U = -\frac{\dot\mu}{\mu} U + f(U), \qquad f(U(0)) = 0,$$
and is in general time-dependent. A perturbation $u = U(t) + \varepsilon\, \psi_k(x) V_k(t)/\mu(t)$ satisfies $\dot V_k = (J(t) - \rho_k(t) D) V_k$, with $J(t)$ the Jacobian of $f$ at $U(t)$.

**Theorem (Theorem 3.3).** Assume $\rho_k \in C^1(I_k)$, $\mu \in C^2(I_k)$, $J \in C^1(I_k)$ and $J_{12}, J_{21} \neq 0$ on an interval $I_k \subseteq (0,\infty)$. If, for all $t \in I_k$,
$$\det J - (d_2 J_{11} + d_1 J_{22}) \rho_k + d_1 d_2 \rho_k^2 < -\frac{\ddot\mu}{\mu} - \big( (d_1 + d_2)\rho_k - \mathrm{tr} J \big) \frac{\dot\mu}{\mu} + \max\{ M_1, M_2 \},$$
$$M_1 = \frac{\dot\mu}{\mu} \frac{\dot J_{12}}{J_{12}} - J_{12} \frac{d}{dt}\Big( \frac{d_1 \rho_k - J_{11}}{J_{12}} \Big), \qquad M_2 = \frac{\dot\mu}{\mu} \frac{\dot J_{21}}{J_{21}} - J_{21} \frac{d}{dt}\Big( \frac{d_2 \rho_k - J_{22}}{J_{21}} \Big),$$
then the uniform state is linearly unstable to the $k$-th mode on $I_k$: the corresponding component of $V_k/\mu$ grows exponentially there. This is a sufficient condition and can hold on a bounded $I_k$ only (transient instability), which is what selects patterns on growing domains.

**Static limit.** If the domain is static ($\dot\mu = \ddot\mu = 0$, $\rho_k$ and $J$ constant), the condition reduces to
$$\det J - (d_2 J_{11} + d_1 J_{22}) \rho_k + d_1 d_2 \rho_k^2 < 0,$$
the classical Turing condition; on a flat domain $\rho_k = |k|^2$.

The analogous result for systems with a polynomial operator $P(\nabla^2_{\Omega(t)})$ in place of $\nabla^2_{\Omega(t)}$ (Swift-Hohenberg type) is Theorem 3.4, obtained by replacing $-\rho_k$ with $P(-\rho_k)$.

## Depends on

- [Riccati comparison bound for growth of a second-order non-autonomous linear ODE](riccati-comparison-growth-bound.md)
- [Dispersion polynomial](dispersion-det.md)
- [Diffusion-driven instability (Turing 1952)](turing-instability.md)

## Expansion

For $n = 2$ the mode equations are $\dot V_1 = (J_{11} - d_1\rho_k) V_1 + J_{12} V_2$ and $\dot V_2 = J_{21} V_1 + (J_{22} - d_2\rho_k) V_2$. Since $J_{12} \neq 0$, eliminating $V_2$ gives a scalar equation $\ddot V_1 + F \dot V_1 + G V_1 = 0$ with
$$F = (d_1 + d_2)\rho_k - \mathrm{tr} J - \frac{\dot J_{12}}{J_{12}}, \qquad G = \det J - (d_2 J_{11} + d_1 J_{22})\rho_k + d_1 d_2 \rho_k^2 + J_{12} \frac{d}{dt}\Big( \frac{d_1\rho_k - J_{11}}{J_{12}} \Big).$$
The comparison criterion (26) with scale $\mu$ gives exponential growth of $V_1/\mu$; eliminating $V_1$ instead (using $J_{21} \neq 0$) gives the $M_2$ branch, and either suffices, hence the maximum. The base state is perturbed around the diluted kinetics rather than around a fixed equilibrium, so the history of growth enters through $\mu$ and through $J(t)$.

## Sources

- R. A. Van Gorder, V. Klika and A. L. Krause, Turing conditions for pattern forming systems on evolving manifolds, *J. Math. Biol.* (2021), Sections 2-3, <https://doi.org/10.1007/s00285-021-01552-y>; preprint <https://arxiv.org/abs/1904.09683> (theorem and equation numbers follow the preprint).
