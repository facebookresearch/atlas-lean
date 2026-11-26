# Kinetic stability of the diluted homogeneous state on a growing domain

This page covers Section 3.4 of Van Gorder, Klika and Krause (2021): the analogue, for a domain whose volume changes in time, of the "stable without diffusion" half of the Turing conditions. Notation is as on [Turing instability conditions on an evolving manifold](turing-conditions-on-evolving-manifolds.md): two species, kinetics $f$, dilution rate $\dot\mu/\mu$, and spatially uniform base state solving $\dot U = -(\dot\mu/\mu) U + f(U)$.

**Asymptotically constant dilution (eqs. (54)-(57)).** Suppose $\dot\mu/\mu \to \nu \in \mathbb{R}$ as $t \to \infty$ (for example exponential growth). Then the base-state equation is asymptotically autonomous with limiting system

$$\dot U = -\nu U + f(U),$$

whose equilibria are the roots $U^\dagger$ of $-\nu U + f(U) = 0$, not the roots $U^*$ of $f(U) = 0$; the two coincide when $\nu = 0$. The limiting system need not have an attracting equilibrium (it may, for example, have a stable limit cycle), and the base state need not converge to an equilibrium. **If** $U^\dagger$ is an equilibrium of the limiting system and $J = \partial f/\partial U$ at $U^\dagger$, its linearisation is $\dot V = (J - \nu I) V$, which is asymptotically stable (Hurwitz) if and only if

$$\mathrm{tr}(J - \nu I) = \mathrm{tr} J - 2\nu < 0, \qquad \det(J - \nu I) = \det J - \nu\, \mathrm{tr} J + \nu^2 > 0 .$$

These strict conditions imply that $U^\dagger$ is locally asymptotically stable for the limiting system; they are conditions on the linearisation, not necessary conditions for nonlinear stability, which can hold at a nonhyperbolic equilibrium where one of them is an equality. For $\nu = 0$ they are the static conditions $\mathrm{tr} J < 0$, $\det J > 0$.

**General dilution (eq. (58)).** Without a limiting rate, apply the theorem on [Turing instability conditions on an evolving manifold](turing-conditions-on-evolving-manifolds.md) to the homogeneous mode $k = 0$ ($\rho_0 = 0$, constant eigenfunction), where $F_i = -\mathrm{tr} J - \dot J_{ij}/J_{ij}$ and $G_i = \det J - J_{ij}\, \tfrac{d}{dt}(J_{ii}/J_{ij})$, assuming $J \in C^1$ and $J_{12}, J_{21} \ne 0$ along the base state. If for some $t_0 \ge 0$, some fixed $\delta > 0$ and one $i \in \{1, 2\}$

$$G_i(t) \le -\frac{\ddot\mu}{\mu} - \Big(\frac{\dot\mu}{\mu} + \delta\Big) F_i(t) - 2\delta\frac{\dot\mu}{\mu} - \delta^2 \quad \text{for all } t \ge t_0,$$

then the spatially uniform linearisation about the base state has a solution $W$ with $|W_i(t)| \ge e^{\delta t}$ for $t \ge t_0$, so the time-varying base state is linearly unstable. Consequently, if every solution of that linearisation is bounded, then for every $\delta > 0$, every $t_0 \ge 0$ and each $i$ the displayed inequality fails at some $t \ge t_0$.

Dilution can therefore shift both the homogeneous state and its stability: a kinetic equilibrium that is stable on a static domain need not be stable, or even relevant, on a growing one.

## Depends on

- [Turing instability conditions on an evolving manifold](turing-conditions-on-evolving-manifolds.md)

## Expansion

For constant $\nu$ the limiting system is autonomous, and the eigenvalues of $J - \nu I$ are those of $J$ shifted by $-\nu$; the trace-determinant test for a $2 \times 2$ real matrix gives the Hurwitz conditions, and the linearisation theorem gives local asymptotic stability when they hold. In the general case the mode $k = 0$ has $\rho_0 = 0$, so the evolving-manifold theorem applies with $F_i$ and $G_i$ evaluated at $\rho_k = 0$; its conclusion $(V_0)_i/\mu \ge e^{\delta t}$ is the stated growth of $W = V_0/\mu$. The source's eq. (58) states a pointwise reversed inequality as a necessary condition; that relies on a decay converse of the comparison principle, which fails (see [Riccati comparison bound](riccati-comparison-growth-bound.md)), so only the contrapositive of the growth statement is recorded here.

## Sources

- R. A. Van Gorder, V. Klika and A. L. Krause, Turing conditions for pattern forming systems on evolving manifolds, *J. Math. Biol.* (2021), Section 3.4, <https://doi.org/10.1007/s00285-021-01552-y>; preprint <https://arxiv.org/abs/1904.09683> (equation numbers follow the preprint).
