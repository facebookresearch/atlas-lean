# Turing instability conditions on an evolving manifold

This page covers Theorem 3.3 of Van Gorder, Klika and Krause (2021), which generalises the Turing condition from a static domain to a smoothly evolving one, here with a fixed exponential growth rate in the comparison step.

**Setting.** Let $\Omega_0 \subset \mathbb R^N$ be a compact, simply connected, smooth $n$-dimensional Riemannian manifold, and let $\Omega(t)$ evolve from it by isotropic dilation, $X = r(t)\, x$ for $x \in \Omega_0$, with $r \in C^2$ positive and $r(0) = 1$. (More generally, any evolution under which the pulled-back [Laplace–Beltrami operators](../../../Geometry/riemannian-geometry/laplace-beltrami-operator/laplacian.md) $\nabla^2_{\Omega(t)}$ share one time-independent eigenbasis $\psi_k$ of $\Omega_0$ will do. A spatially uniform volume change is not enough: unequal coordinate stretching of a disk gives the operator $r_1^{-2}\partial_{xx} + r_2^{-2}\partial_{yy}$, whose eigenfunctions change with time and couple the modes.) A two-species system $u = (u_1, u_2)$ obeys conservation with advection by the domain velocity $Q$,

$$\partial_t u + \nabla_{\Omega(t)} \cdot (Q u) = D\, \nabla^2_{\Omega(t)} u + f(u), \qquad D = \mathrm{diag}(d_1, d_2),$$

with no-flux boundary conditions if $\partial\Omega(t) \neq \emptyset$. Write $\mu(t) = r(t)^n$ for the volume ratio, so $\dot\mu/\mu$ is the dilation rate, and let $0 = \rho_0(t) < \rho_1(t) \le \rho_2(t) \le \cdots$ be the eigenvalues of $-\nabla^2_{\Omega(t)}$ with eigenfunctions $\psi_k$ (in Lagrangian coordinates), so that $\rho_k(t) = \rho_k(0)/r(t)^2$.

The spatially uniform base state solves the diluted kinetics

$$\dot U = -\frac{\dot\mu}{\mu} U + f(U), \qquad f(U(0)) = 0,$$

and is in general time-dependent. A perturbation $u = U(t) + \varepsilon\, \psi_k V_k(t)/\mu(t)$ satisfies, to first order, $\dot V_k = (J(t) - \rho_k(t) D) V_k$, with $J(t)$ the Jacobian of $f$ at $U(t)$; distinct modes do not interact.

**Theorem (after Theorem 3.3).** Let $I_k = [t_0, t_1) \subseteq [0, \infty)$, and assume $\mu \in C^2(I_k)$, $J \in C^1(I_k)$ and $J_{12}, J_{21} \neq 0$ on $I_k$. For $(i, j) = (1, 2)$ and $(2, 1)$ set

$$F_i = (d_1 + d_2)\rho_k - \mathrm{tr} J - \frac{\dot J_{ij}}{J_{ij}}, \qquad G_i = \det J - (d_2 J_{11} + d_1 J_{22}) \rho_k + d_1 d_2 \rho_k^2 + J_{ij} \frac{d}{dt}\Big( \frac{d_i \rho_k - J_{ii}}{J_{ij}} \Big).$$

If for some fixed $\delta > 0$ and one $i \in \{1, 2\}$

$$G_i(t) \le -\frac{\ddot\mu}{\mu} - \Big(\frac{\dot\mu}{\mu} + \delta\Big) F_i(t) - 2\delta\frac{\dot\mu}{\mu} - \delta^2 \quad \text{for all } t \in I_k,$$

then the mode-$k$ linearisation has a solution whose $i$-th component satisfies $(V_k)_i(t)/\mu(t) \ge e^{\delta t}$ on $I_k$: the perturbation $\psi_k V_k/\mu$ of the uniform state grows at least exponentially, at rate $\delta$, on $I_k$. This is a sufficient condition and can hold on a bounded $I_k$ only (transient instability), which is what selects patterns on growing domains. In the source's notation, $G_i < -\ddot\mu/\mu - (\dot\mu/\mu) F_i$ is the source's condition with $M_i = (\dot\mu/\mu)(\dot J_{ij}/J_{ij}) - J_{ij}\, \tfrac{d}{dt}\big((d_i\rho_k - J_{ii})/J_{ij}\big)$ in place of $\max\{M_1, M_2\}$; the theorem above asks in addition for the margin $\delta(F_i + 2\dot\mu/\mu) + \delta^2$ with $\delta > 0$ fixed, since a pointwise strict inequality at $\delta = 0$ does not give exponential growth.

**Static limit.** If the domain is static ($\mu \equiv 1$, $\rho_k$ and $J$ constant) and $\mathrm{tr} J < 0$, $F_i = (d_1 + d_2)\rho_k - \mathrm{tr} J$, $G_i = \det(J - \rho_k D)$, and the condition becomes $\delta^2 + F_i\delta + \det(J - \rho_k D) \le 0$. Some $\delta > 0$ satisfies it if and only if

$$\det J - (d_2 J_{11} + d_1 J_{22}) \rho_k + d_1 d_2 \rho_k^2 < 0,$$

the classical Turing condition; on a flat domain $\rho_k = |k|^2$.

The analogous result for systems with a polynomial operator $P(\nabla^2_{\Omega(t)})$ in place of $\nabla^2_{\Omega(t)}$ (Swift-Hohenberg type) is the source's Theorem 3.4, obtained by replacing $-\rho_k$ with $P(-\rho_k)$.

## Depends on

- [Laplace–Beltrami operator](../../../Geometry/riemannian-geometry/laplace-beltrami-operator/laplacian.md)
- [Dispersion polynomial](dispersion-det.md)
- [Diffusion-driven instability (Turing 1952)](turing-instability.md)

## Proof depends on

- [Riccati comparison bound for growth of a second-order non-autonomous linear ODE](riccati-comparison-growth-bound.md)

## Expansion

Isotropic dilation pulls $\nabla^2_{\Omega(t)}$ back to $r(t)^{-2}\nabla^2_{\Omega_0}$, so the $\psi_k$ stay eigenfunctions and the linearisation $\partial_t w + (\dot\mu/\mu) w = D\nabla^2_{\Omega(t)} w + J w$ separates; substituting $w = \psi_k V_k/\mu$ removes the dilation term. For the two species the mode equations are $\dot V_1 = (J_{11} - d_1\rho_k) V_1 + J_{12} V_2$ and $\dot V_2 = J_{21} V_1 + (J_{22} - d_2\rho_k) V_2$. Since $J_{12} \neq 0$, eliminating $V_2$ gives the scalar equation $\ddot V_1 + F_1 \dot V_1 + G_1 V_1 = 0$, and every initial value $(V_1, \dot V_1)(t_0)$ comes from a solution of the system. The comparison corollary with scale $\mu$ and rate $\delta$ gives a solution with $V_1 \ge \mu e^{\delta t}$. Eliminating $V_1$ instead (using $J_{21} \neq 0$) gives the $i = 2$ branch. The base state is perturbed around the diluted kinetics rather than around a fixed equilibrium, so the history of growth enters through $\mu$ and through $J(t)$. In the static case the condition is a quadratic in $\delta$ with value $\det(J - \rho_k D)$ at $\delta = 0$ and, because $\mathrm{tr} J < 0$, nonnegative slope $F_i$ there, which gives the equivalence.

## Sources

- R. A. Van Gorder, V. Klika and A. L. Krause, Turing conditions for pattern forming systems on evolving manifolds, *J. Math. Biol.* (2021), Sections 2-3, <https://doi.org/10.1007/s00285-021-01552-y>; preprint <https://arxiv.org/abs/1904.09683> (theorem and equation numbers follow the preprint).
