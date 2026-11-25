# JKO step

A probability density $\rho$ is a JKO step from $\rho_0$ with time step $h$ if $\rho$ is
[admissible](is-admissible.md) and minimizes the [JKO objective](jko-objective.md)
$\tfrac12 W_2(\rho_0, \cdot)^2 + h F$ over all admissible densities. It is the
[minimizing-movement step](../minimizing-movements/is-minimizing-movement-step.md) of the free energy in the Wasserstein
space, restricted to admissible densities.

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, scheme (13).
