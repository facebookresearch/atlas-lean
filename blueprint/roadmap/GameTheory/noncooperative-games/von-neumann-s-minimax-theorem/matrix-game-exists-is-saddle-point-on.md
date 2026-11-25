# Saddle point of a matrix game

Let $m, n \ge 1$ and let $A$ be a real $m \times n$ matrix, the payoff matrix of a two-player
zero-sum game in which the row player receives $p^{\mathsf{T}} A q$ from the column player when
they play the mixed strategies $p \in \Delta_m$ and $q \in \Delta_n$ (points of the standard
simplices). Then there are $p^\star \in \Delta_m$ and $q^\star \in \Delta_n$ with

$$p^{\mathsf{T}} A q^\star \le p^{\star\mathsf{T}} A q^\star \le p^{\star\mathsf{T}} A q
\quad\text{for all } p \in \Delta_m,\ q \in \Delta_n,$$

that is, $p^\star$ is a best response to $q^\star$ and $q^\star$ is a best response to $p^\star$:
$(p^\star, q^\star)$ is a mixed Nash equilibrium of the zero-sum game.

The proof specialises Sion's minimax theorem to the bilinear payoff on the product of the two simplices.

## Background

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md):
  background, the classical alternative proof, in which the optimal strategies of the two players
  are optimal solutions of a primal–dual pair of linear programs.

## Sources

- J. von Neumann, "Zur Theorie der Gesellschaftsspiele", Math. Ann. 100 (1928), 295–320.
- M. Sion, "On general minimax theorems", Pacific J. Math. 8 (1958), 171–176.
