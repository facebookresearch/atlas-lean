# Convergence of the JKO scheme to the Fokker–Planck equation

Under the assumptions of [existence and uniqueness of the JKO step](exists-unique-is-jkostep.md),
let $\beta > 0$ and let $\rho_0$ be [admissible](is-admissible.md) with finite
[free energy](free-energy.md). For $h > 0$ let $(\rho_h^{(k)})$ be the [JKO sequence](is-jkosequence.md)
started at $\rho_0$ and $\rho_h(t) = \rho_h^{(k)}$ for $t \in [kh, (k+1)h)$. Then, as $h \downarrow 0$,
$\rho_h(t) \rightharpoonup \rho(t)$ weakly in $L^1$ for every $t > 0$, where $\rho$ is $C^\infty$ on
$(0, \infty) \times \mathbb{R}^n$ and solves

$$\partial_t \rho = \operatorname{div}(\rho \nabla \Psi) + \beta^{-1} \Delta \rho,$$

with $\rho(t) \to \rho_0$ strongly in $L^1$ as $t \downarrow 0$ and with the second moment and the
potential energy of $\rho(t)$ in $L^\infty(0, T)$ for every $T$.

Here the divergence is written as $\langle \nabla \rho, \nabla \Psi \rangle + \rho \Delta \Psi$, the
convergence is asserted for every family of JKO sequences started at $\rho_0$, and weak $L^1$
convergence is tested against bounded measurable functions. The paper also states that $\rho$ is
the unique such solution; that uniqueness is not part of the statement above.

This is the precise sense in which the Fokker–Planck equation is the gradient flow of the free
energy for the Wasserstein distance.

## Informally uses

- [Discrete energy inequality of the JKO scheme](../minimizing-movements/energy-sum-le.md): the summed one-step comparison
  just before (46), from which JKO obtain the a priori estimate (42).
- [Hölder-½ estimate of the JKO scheme](../minimizing-movements/dist-sq-le.md): the second and third lines of (46), from the triangle
  and Cauchy–Schwarz inequalities.
- [Existence and uniqueness of the JKO step](exists-unique-is-jkostep.md): the scheme is well
  defined (Proposition 4.1).

## Background

- [Fokker–Planck equation](../../../../Probability/stochastic-calculus/fokker-planck-equation/README.md): the dissipation identity and the Gibbs stationary density.

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, Theorem 5.1 with (31), (32) and (33).
