# Reading an optimal dual solution from the final simplex dictionary

For a linear program $\max\{c^\top x : Ax \le b,\ x \ge 0\}$ with $b \ge 0$ over a linearly ordered field, represented by its slack dictionary, if the simplex method with Bland's rule stops at an optimal dictionary, then minus the reduced costs of the slack variables form a vector $y \ge 0$ with $A^\top y \ge c$ and $b^\top y$ equal to the optimal value; that is, an optimal dual solution, certifying strong duality. Applied to the linear program of a finite zero-sum game, this computes the value and optimal mixed strategies of both players.

## Proof sketch

The final objective row expresses $c^\top x$ as $z_0 - \sum_j \bar c_j x_j$ with $\bar c \ge 0$; comparing coefficients of the slack variables with the original equations gives the dual feasibility and the equality $z_0 = b^\top y$.

## Depends on

- [Simplex dictionaries and pivoting](simplex-dictionaries.md)
- [Zero-sum value as a linear program](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/zero-sum-value-as-a-linear-program.md)

## Proof depends on

- [Termination and correctness of the simplex method with Bland's rule](../../graph-algorithms/linear-programming-and-flows/termination-and-correctness-of-the-simplex.md)

## Sources

- V. Chvátal, "Linear Programming", W. H. Freeman, 1983.
- J. Matoušek and B. Gärtner, "Understanding and Using Linear Programming", Springer, 2007.
