# The folk theorem of evolutionary game dynamics

For a symmetric game with payoff matrix $A$ and the replicator equation $\dot x_i = x_i((Ax)_i - x\cdot Ax)$ on $S_n$, call $z$ a Nash equilibrium if $y\cdot Az \le z\cdot Az$ for all $y \in S_n$, and strict if equality holds only for $y = z$. Then (a) every Nash equilibrium is a rest point; (b) every strict Nash equilibrium is asymptotically stable, which is a case of the [Lyapunov characterization of evolutionarily stable states](../../../Biology/population-dynamics/replicator-dynamics/ess-lyapunov-function-for-the-replicator-equation.md) because a strict Nash equilibrium is an evolutionarily stable strategy; (c) if a rest point is the limit of an interior orbit as $t \to \infty$, it is a Nash equilibrium; (d) every stable rest point is a Nash equilibrium. None of the converse statements holds, and every interior rest point is a Nash equilibrium (Hofbauer and Sigmund 2003, Sec. 2.3, the folk theorem of evolutionary game theory). At a boundary rest point $z$, $(Az)_i - z\cdot Az$ is the eigenvalue of the Jacobian transversal to the face $x_i = 0$, so $z$ is a Nash equilibrium if and only if all its transversal eigenvalues are nonpositive.

## Depends on

- [Solution of the replicator equation](../../../Biology/population-dynamics/replicator-dynamics/is-solution.md)
- [Rest point of the replicator equation](../../../Biology/population-dynamics/replicator-dynamics/is-rest-point.md)

## Proof depends on

- [Lyapunov characterization of evolutionarily stable states for the replicator equation](../../../Biology/population-dynamics/replicator-dynamics/ess-lyapunov-function-for-the-replicator-equation.md)

## Expansion

1. Rest points of the replicator equation as the points with $(Ax)_i = x\cdot Ax$ on the support; Nash equilibria of symmetric games.
2. (a) from the equal-payoff property on the support.
3. (b) as a corollary: a strict Nash equilibrium is a pure evolutionarily stable strategy, and every evolutionarily stable strategy is asymptotically stable.
4. (c) and (d) by contradiction: a strategy $i$ with $(Az)_i > z\cdot Az$ would grow near $z$; the transversal eigenvalues.
5. Counterexamples to the converses (for instance the rock–paper–scissors game with $\det A < 0$, whose interior Nash equilibrium is not stable).

## Sources

- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. 40 (2003), 479–519, Sec. 2.3. <https://doi.org/10.1090/S0273-0979-03-00988-1>
