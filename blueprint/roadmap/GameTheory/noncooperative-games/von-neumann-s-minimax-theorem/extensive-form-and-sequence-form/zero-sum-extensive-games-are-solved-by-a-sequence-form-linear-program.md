# Zero-sum extensive games are solved by a sequence-form linear program

In a two-player zero-sum extensive-form game with perfect recall and sequence-form payoff matrix $A$ for player $1$, the max-min value over behavior strategies equals the min-max value, and an optimal realization plan $x$ of player $1$ is obtained from an optimal solution $(x, q)$ of the linear program: maximize $f^\top q$ subject to $F^\top q \le A^\top x$, $Ex = e$, $x \ge 0$, where $Fy = f$, $y \ge 0$ are player $2$'s realization-plan constraints. Its size is linear in the game tree, its optimal value is the value of the game, and symmetrically for player $2$. Weak duality holds for every pair of feasible plans.

## Proof sketch

Replace the inner minimization by the dual of player $2$'s best-response program; the resulting joint program is linear and its optimum is the max-min value. Symmetrically for player $2$, and LP duality equates the two values.

## Depends on

- [Sequence-form payoff matrices](sequence-form-payoff-matrices.md)
- [Von Neumann's minimax theorem](../matrix-game-minimax.md)

## Proof depends on

- [Sequence-form best responses are linear programs](sequence-form-best-responses-are-linear-programs.md)
- [The realization plan polytope is the convex hull of pure realization plans](the-realization-plan-polytope-is-the-convex-hull-of-pure-realization-plans.md)

## Sources

- Bernhard von Stengel, "Efficient Computation of Behavior Strategies", Games and Economic Behavior, 1996.
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
