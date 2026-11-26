# Linear feasibility with integer data reduces to a single symmetric zero-sum game

Let $A$ be an $m \times n$ integer matrix and $b \in \mathbb{Z}^m$, with all entries of absolute value at most $B$, and work over any linearly ordered field. Let

$$
\beta \ge n \cdot n! \cdot (mB^2 + 1)^n .
$$

Then every solution $(y, v, x, u, t)$ of the Dantzig game associated with $F(\hat A, \hat b(\beta))$, a symmetric game with $m + n + 5$ pure strategies built from the data alone, has $t > 0$; if $u = 0$ then the first $n$ coordinates of $x/t$ solve $Ax = b$, $x \ge 0$, and if $u > 0$ the system has no nonnegative solution. Since symmetric games always have solutions, linear feasibility with integer data is solved by solving one symmetric zero-sum game.

## Proof sketch

By Cramer's rule and Leibniz's bound on determinants, if $Ax = b$, $x \ge 0$ is solvable it has a solution of total weight at most $\beta$, so $F(A,b)$ and the bounded problem are solvable together. The bounded game has only solutions with $t > 0$, and the case analysis on $u$ resolves the bounded problem, hence $F(A,b)$. Existence of a solution comes from the symmetric minimax theorem.

## Depends on

- [Adler's Dantzig game of a linear feasibility problem](adler-feasibility-game.md)

## Proof depends on

- [The Dantzig game of a bounded feasibility problem has no solution with t = 0](bounded-feasibility-game-positive-t.md)
- [Every symmetric zero-sum game has a solution](every-symmetric-game-has-a-solution.md)

## Sources

- Ilan Adler, "The equivalence of linear programs and zero-sum games", International Journal of Game Theory 42(1), 165-177, 2013.
