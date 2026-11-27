# Von Neumann's minimax theorem

Let $m, n \ge 1$ and let $A$ be a real $m \times n$ matrix, the payoff matrix of a two-player
zero-sum game in which the row player maximises and the column player minimises the expected
payoff $p^{\mathsf{T}} A q$ over mixed strategies $p \in \Delta_m$ and $q \in \Delta_n$. Then

$$\max_{p \in \Delta_m} \min_{q \in \Delta_n} p^{\mathsf{T}} A q
= \min_{q \in \Delta_n} \max_{p \in \Delta_m} p^{\mathsf{T}} A q .$$

Both sides are, a priori, a supremum of infima and an infimum of suprema over the simplices; the
saddle point of the game attains them. The common value is the value of the game.

## Informally uses

- [Saddle point of a matrix game](matrix-game-exists-is-saddle-point-on.md): the saddle point
  attains both sides.

## Background

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md):
  background, the theorem is equivalent to the duality of a pair of linear programs (Dantzig 1951).
- [Hedge algorithm](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/README.md):
  background, Freund and Schapire's learning proof: if both players run a no-regret algorithm
  such as Hedge, their average strategies are approximately optimal, which gives the theorem in the
  limit.

## Sources

- J. von Neumann, "Zur Theorie der Gesellschaftsspiele", Math. Ann. 100 (1928), 295–320.
- Y. Freund and R. E. Schapire, "Adaptive game playing using multiplicative weights",
  Games Econom. Behav. 29 (1999), 79–103.
