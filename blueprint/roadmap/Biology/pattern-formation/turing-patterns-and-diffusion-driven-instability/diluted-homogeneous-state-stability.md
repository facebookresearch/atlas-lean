# Kinetic stability of the diluted homogeneous state on a growing domain

This page covers Section 3.4 of Van Gorder, Klika and Krause (2021): the analogue, for a domain whose volume changes in time, of the "stable without diffusion" half of the Turing conditions. Notation is as on [Turing instability conditions on an evolving manifold](turing-conditions-on-evolving-manifolds.md): two species, kinetics $f$, dilution rate $\dot\mu/\mu$, and spatially uniform base state solving $\dot U = -(\dot\mu/\mu) U + f(U)$.

**Asymptotically constant dilution (eqs. (54)-(57)).** Suppose $\dot\mu/\mu \to \nu \in \mathbb{R}$ as $t \to \infty$ (for example exponential growth). The large-time base state is then a root $U^\dagger$ of

$$-\nu U + f(U) = 0,$$

not a root $U^*$ of $f(U) = 0$; the two coincide when $\nu = 0$. With $J = \partial f/\partial U$ at $U^\dagger$, the linearisation is $\dot V = (J - \nu I) V$, and the usual necessary conditions for $U^\dagger$ to be asymptotically stable become

$$\mathrm{tr}(J - \nu I) = \mathrm{tr} J - 2\nu < 0, \qquad \det(J - \nu I) = \det J - \nu\, \mathrm{tr} J + \nu^2 > 0 .$$

For $\nu = 0$ these are the static conditions $\mathrm{tr} J < 0$, $\det J > 0$.

**General dilution (eq. (58)).** Without a limiting rate, the base state is perturbed along the homogeneous mode $k = 0$ ($\rho_0 = 0$), and the decay half of the comparison principle gives the necessary condition for stability of the time-varying base state:

$$\det J > -\frac{\ddot\mu}{\mu} + \mathrm{tr} J\, \frac{\dot\mu}{\mu} + \max\Big\{ \frac{\dot\mu}{\mu}\frac{\dot J_{12}}{J_{12}} + J_{12} \frac{d}{dt}\frac{J_{11}}{J_{12}},\ \frac{\dot\mu}{\mu}\frac{\dot J_{21}}{J_{21}} + J_{21} \frac{d}{dt}\frac{J_{22}}{J_{21}} \Big\},$$

which is the complement of the instability condition of Theorem 3.3 at $k = 0$.

Dilution can therefore shift both the homogeneous state and its stability: a kinetic equilibrium that is stable on a static domain need not be stable, or even relevant, on a growing one.

## Depends on

- [Turing instability conditions on an evolving manifold](turing-conditions-on-evolving-manifolds.md)
- [Riccati comparison bound for growth of a second-order non-autonomous linear ODE](riccati-comparison-growth-bound.md)

## Expansion

For constant $\nu$ the base-state equation is autonomous at large times, so standard trace-determinant conditions apply to $J - \nu I$, whose eigenvalues are those of $J$ shifted by $-\nu$. In the general case, setting $\rho_k = 0$ in the scalar second-order equation obtained by eliminating one component of the mode equations, and applying the decay statement (Theorem 3.2) instead of the growth statement, reverses the inequality of Theorem 3.3.

## Sources

- R. A. Van Gorder, V. Klika and A. L. Krause, Turing conditions for pattern forming systems on evolving manifolds, *J. Math. Biol.* (2021), Section 3.4, <https://doi.org/10.1007/s00285-021-01552-y>; preprint <https://arxiv.org/abs/1904.09683> (equation numbers follow the preprint).
