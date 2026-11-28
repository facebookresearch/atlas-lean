# Nash equilibria among the rest points of the replicator equation

For a symmetric game with payoff matrix $A$ and the replicator equation $\dot x_i = x_i((Ax)_i - x\cdot Ax)$ on $S_n$, call $z$ a Nash equilibrium if $y\cdot Az \le z\cdot Az$ for all $y \in S_n$. The four parts of the folk theorem of evolutionary game theory are stated as [Folk theorem (a)](../folk-theorem-of-evolutionary-game-theory/replicator-field-eq-zero.md), [(b)](../folk-theorem-of-evolutionary-game-theory/asymptotically-stable.md), [(c)](../folk-theorem-of-evolutionary-game-theory/is-nash-of-tendsto.md) and [(d)](../folk-theorem-of-evolutionary-game-theory/is-nash-of-is-lyapunov-stable.md) (Hofbauer and Sigmund 2003, Sec. 2.3). Two further facts from the same section characterize Nash equilibria among the rest points: every interior rest point is a Nash equilibrium, since all $(Az)_i$ are then equal to $z\cdot Az$; and at a boundary rest point $z$, $(Az)_i - z\cdot Az$ for $z_i = 0$ is the eigenvalue of the Jacobian transversal to the face $x_i = 0$, so $z$ is a Nash equilibrium if and only if all its transversal eigenvalues are nonpositive.

## Depends on

- [Rest point of the replicator equation](../../../Biology/population-dynamics/replicator-dynamics/is-rest-point.md)
- [Symmetric Nash equilibrium of a matrix game](../stability-of-evolutionarily-stable-states/is-nash.md)
- [Replicator Jacobian](../stability-of-boundary-evolutionarily-stable-stra/replicator-jacobian.md)

## Expansion

1. Rest points of the replicator equation as the points with $(Ax)_i = x\cdot Ax$ on the support.
2. Interior rest points as Nash equilibria.
3. The Jacobian at a boundary rest point, its transversal eigenvalues $(Az)_i - z\cdot Az$, and the characterization of Nash equilibria by their signs.
4. Counterexamples to the converses of the folk theorem (for instance the rock–paper–scissors game with $\det A < 0$, whose interior Nash equilibrium is not stable).

## Sources

- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. 40 (2003), 479–519, Sec. 2.3. <https://doi.org/10.1090/S0273-0979-03-00988-1>
