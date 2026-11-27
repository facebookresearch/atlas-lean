# Permanence of replicator equations by average Lyapunov functions

The replicator equation $\dot x_i = x_i((Ax)_i - x\cdot Ax)$ on $S_n$ is permanent if there is a compact set $K$ in the interior of $S_n$ such that every interior orbit eventually stays in $K$. Hofbauer and Sigmund (2003, Theorem 5) state the criterion: the replicator equation is permanent if there exists $p$ in the interior of $S_n$ with

$$p\cdot Ab > b\cdot Ab$$

for all rest points $b$ on the boundary of $S_n$. Since the rest points on the boundary form a finite union of convex sets, it suffices to check the inequality at their extreme points, which gives a finite system of linear inequalities for $p$. For monocyclic payoff matrices ($a_{ii} = 0$, $a_{ij} > 0$ if $i = j + 1 \bmod n$, $a_{ij} \le 0$ otherwise) the replicator equation is permanent if and only if there is an interior rest point $z$ with $z\cdot Az > 0$ (their Theorem 6).

## Depends on

- [Solution of the replicator equation](is-solution.md)
- [Rest point of the replicator equation](is-rest-point.md)

## Expansion

1. The model and the definition of permanence.
2. Average Lyapunov functions: the function $P(x) = \prod_i x_i^{p_i}$ vanishes on the boundary, and $\dot P/P = p\cdot Ax - x\cdot Ax$; the criterion that a function vanishing on the boundary and increasing on average along boundary orbits implies permanence.
3. The reduction of the average-increase condition to boundary rest points, using time averages of boundary orbits.
4. Monocyclic matrices and the coincidence of the necessary and sufficient conditions (Theorems 4 and 6 of the source).
5. The Lotka–Volterra version (dissipative systems with $\sum_i p_i(r_i + (Az)_i) > 0$ at every boundary equilibrium $z$), via the correspondence between replicator and Lotka–Volterra systems, as a separate statement.

## Sources

- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. 40 (2003), 479–519, Sec. 2.5, Theorems 4–6. <https://doi.org/10.1090/S0273-0979-03-00988-1>
