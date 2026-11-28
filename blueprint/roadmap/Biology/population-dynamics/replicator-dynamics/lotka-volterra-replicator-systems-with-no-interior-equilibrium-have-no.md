# No interior equilibrium means no interior limit points

For the replicator equation $\dot x_i = x_i((Ax)_i - x\cdot Ax)$ on the simplex $S_n$: if there is no rest point in the interior of $S_n$, then every orbit converges to the boundary of $S_n$ (Hofbauer and Sigmund 2003, Theorem 4, last sentence). The same holds for Lotka–Volterra systems through the correspondence of Hofbauer (1981) (Hofbauer and Sigmund 2003, Theorem 3): the map $y_i = x_i/x_n$, $i = 1, \dots, n - 1$, from $\{x \in S_n : x_n > 0\}$ onto $\mathbb{R}^{n-1}_+$ maps orbits of the replicator equation onto orbits of $\dot y_i = y_i (r_i + \sum_j c_{ij} y_j)$ with $r_i = a_{in} - a_{nn}$ and $c_{ij} = a_{ij} - a_{nj}$; so an $(n-1)$-species Lotka–Volterra system with no equilibrium in the open positive orthant has no interior orbit with an $\omega$-limit point in the open orthant.

## Depends on

- [Solution of the replicator equation](../../../Biology/population-dynamics/replicator-dynamics/is-solution.md)
- [Rest point of the replicator equation](is-rest-point.md)
- [Generalized Lotka–Volterra vector field](../replicator-and-lotka-volterra-equivalence/lv-field.md)
- [Orbital equivalence, replicator to Lotka–Volterra](../replicator-and-lotka-volterra-equivalence/replicator-orbit-equiv-lotka-volterra.md)
- [Orbital equivalence, Lotka–Volterra to replicator](../replicator-and-lotka-volterra-equivalence/lotka-volterra-orbit-equiv-replicator.md)

## Expansion

1. The replicator equation and Lotka–Volterra systems, and the orbit correspondence of Theorem 3 of the source, with its change of velocity.
2. The separation argument: with no interior equilibrium, the affine map $y \mapsto r + Cy$ misses $0$ on the open orthant, so some vector $c$ has $c\cdot(r + Cy) > 0$ there, and $V(y) = \sum_i c_i \ln y_i$ increases strictly along interior orbits.
3. The conclusion that interior $\omega$-limit points are impossible.
4. The replicator form via the correspondence.

## Sources

- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. 40 (2003), 479–519, Theorems 3 and 4. <https://doi.org/10.1090/S0273-0979-03-00988-1>
- Original result: J. Hofbauer, On the occurrence of limit cycles in the Volterra–Lotka equation, Nonlinear Anal. 5 (1981), 1003–1007. <https://doi.org/10.1016/0362-546x(81)90059-6> The orbit correspondence follows Theorem 3 of Hofbauer and Sigmund (2003).
