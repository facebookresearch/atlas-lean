# Free energy of the Fokker–Planck equation

Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra and
Lebesgue measure $dx$. For a potential $\Psi : E \to \mathbb{R}$ and $\beta \in \mathbb{R}$, the free
energy of a measure $\rho$ on $E$ is

$$F(\rho) = E(\rho) + \beta^{-1} S(\rho) \in [-\infty, +\infty],$$

the [potential energy](potential-energy.md) $E(\rho) = \int \max(\Psi, 0)\, d\rho \in [0, \infty]$ plus
$\beta^{-1}$ times the [negative entropy](neg-entropy.md) $S(\rho)$, with $0^{-1} = 0$,
$0 \cdot (\pm\infty) = 0$ and $\infty + (-\infty) = -\infty$. For an absolutely continuous
$\rho = g\, dx$ with a finite density $g$, $E(\rho) = \int \max(\Psi, 0)\, g \, dx$ and
$S(\rho) = \int g \log g \, dx$; for $\Psi \ge 0$ this is
$F(\rho) = \int \Psi g \, dx + \beta^{-1} \int g \log g \, dx$, equation (5) of the source. Without
absolute continuity the two differ, since $S$ sees only the absolutely continuous part of $\rho$: for
$\rho = \delta_0$ on $\mathbb{R}$, $\Psi = 1$ and $\beta = 1$, $F(\rho) = 1$.

If $\Psi \ge 0$, $\beta > 0$ and $Z = \int e^{-\beta \Psi} dx < \infty$, then for every probability
density $g$ with $E(g\, dx)$ and $S(g\, dx)$ finite,
$F(g\, dx) = \beta^{-1}\big(\mathrm{KL}(g \,\|\, \gamma) - \log Z\big)$, where
$\gamma = Z^{-1} e^{-\beta\Psi}$ is the Gibbs density; so among such densities $F$ is smallest at
$\gamma$ whenever $\gamma$ itself has finite energy and entropy. Jordan, Kinderlehrer and Otto obtain
the solutions of the Fokker–Planck equation
$\partial_t \rho = \operatorname{div}(\rho \nabla \Psi) + \beta^{-1} \Delta \rho$ as limits of the
time-discrete scheme that minimizes $\tfrac12 W_2(\rho_{k-1}, \rho)^2 + h F(\rho)$ at each step.

## Background

- [Free energy of a Fokker–Planck density](../../../../Probability/stochastic-calculus/fokker-planck-equation/free-energy.md):
  the same functional for densities on an interval, with its dissipation identity.

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, equation (5) and Section 2.
