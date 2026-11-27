# Equilibria and monomorphic stability of density games coincide with the replicator equation

Let $n \ge 2$ phenotypes have abundances $x_1, \dots, x_n \ge 0$, total $x_T = \sum_{j} x_j > 0$ and frequencies $y_j = x_j / x_T$. Fix growth rates $r_i > 0$ and a payoff matrix $A = (a_{ij})$ with all $a_{ij} > 0$. The **density game** is

$$\dot x_i = r_i\, x_i \left(1 - \frac{x_T}{K_i}\right), \qquad K_i = \sum_{j=1}^{n} a_{ij}\, y_j, \qquad i = 1, \dots, n,$$

so the game payoff $K_i$ acts as a frequency-dependent carrying capacity, while $r_i$ is the growth rate at low density. Compare it with the replicator equation $\dot y_i = y_i (f_i - \bar f)$, $f_i = \sum_j a_{ij} y_j$, $\bar f = \sum_j y_j f_j$, on the simplex.

**Theorem.**

1. The non-trivial equilibria of the density game ($x \ne 0$) are in bijection with the rest points of the replicator equation: at every such equilibrium all strategies present have the same payoff $K_i = x_T$, and the equilibrium frequencies $y$ are exactly the replicator rest points. In particular they do not depend on $r_1, \dots, r_n$.
2. The monomorphic equilibrium $E_i = a_{ii} e_i$ ($e_i$ the $i$-th unit vector) is asymptotically stable if $a_{ii} > a_{ji}$ for every $j \ne i$; this condition does not involve the growth rates.
3. The origin is an equilibrium that is always unstable.

## Proof sketch

Rewrite the dynamics as $\dot x_i = (r_i / K_i)\, x_i (K_i - x_T)$. Since $r_i / K_i > 0$, a strategy with $x_i > 0$ is at rest iff $K_i = x_T$; all present strategies therefore earn the common payoff $x_T$, which equals the mean payoff, the defining condition of a replicator rest point. At $E_i$ the Jacobian is triangular, with diagonal entries $-r_i$ (stability of the single-phenotype logistic equilibrium) and, for $j \ne i$, $-r_j (a_{ii}/a_{ji} - 1)$. All eigenvalues are negative exactly when $a_{ii} > a_{ji}$ for all $j \ne i$, i.e. when no other phenotype can invade; the positive factor $r_j$ cannot change a sign. This is the same invasion condition as for the replicator equation, and it implies that a strict Nash equilibrium (in particular an ESS with strict inequalities) of $A$ is a stable monomorphic state of the density game. Because $r_i > 0$, every trajectory is pushed away from the origin, so the population never goes extinct.

## Depends on

- [Rest point of the replicator equation](../../../replicator-dynamics/is-rest-point.md)

## Proof depends on

- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- S. Novak, K. Chatterjee and M. A. Nowak, "Density games", *Journal of Theoretical Biology* (2013), Section 2, Eqs. (2)–(4) and Theorem 1, <https://doi.org/10.1016/j.jtbi.2013.05.029> (PMC3753514).
