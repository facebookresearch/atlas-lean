# Linear feasibility with integer data reduces to a single symmetric zero-sum game

Let $A$ be an $m \times n$ integer matrix of rank $m$ with no zero column, $b \in \mathbb{Z}^m$, and $\theta$ the largest absolute value of an entry of $(A, b)$. Let $\hat A$ be $A$ with the row $(1, \dots, 1, 1)$ appended below $(A \mid 0)$ and $\hat b(\beta) = (b, \beta)$, so that $F(\hat A, \hat b(\beta))$ asks for $x \ge 0$, $x_{n+1} \ge 0$ with $Ax = b$ and $\sum_{j \le n} x_j + x_{n+1} = \beta$. Let

$$
\beta \ge m\,(\sqrt{m}\,\theta)^m + 1 .
$$

Then every solution $(x, u, y, v, t)$ of the Dantzig game associated with $F(\hat A, \hat b(\beta))$ has $t > 0$; if $u = 0$ then the first $n$ coordinates of $x/t$ solve $Ax = b$, $x \ge 0$, and if $u > 0$ the system $Ax = b$, $x \ge 0$ has no solution. Since symmetric games always have solutions, linear feasibility with integer data is resolved by solving one symmetric zero-sum game built from the data alone.

## Proof sketch

The bounded problem has only the zero solution of its homogeneous system, so its Dantzig game has no solution with $t = 0$; with $t > 0$ the case analysis on $u$ resolves the bounded problem. If $Ax = b$, $x \ge 0$ is solvable it has a basic solution, whose coordinates are, by Cramer's rule (using $\mathrm{rank}\,A = m$), ratios of $m \times m$ determinants of $(A, b)$; with integer data the denominators have absolute value at least $1$ and the numerators at most $(\sqrt{m}\,\theta)^m$, so some solution has total weight below $\beta$ and the bounded problem is solvable exactly when the original one is. Existence of a solution comes from the symmetric minimax theorem.

The following count is derived here from the source's definitions. The Dantzig game of $F(A, b)$ has strategies $(y, v, x, u, t)$, that is, $m + n + 3$ of them, so the game of $F(\hat A, \hat b(\beta))$ has $m + n + 5$ pure strategies (the source's overview of its Karp-type reduction speaks of a payoff matrix of size $(m + n + 4) \times (m + n + 4)$).

## Depends on

- [Adler's Dantzig game of a linear feasibility problem](adler-feasibility-game.md)
- [Symmetric zero-sum game and its solutions](symmetric-zero-sum-game.md)

## Proof depends on

- [The Dantzig game of a bounded feasibility problem has no solution with t = 0](bounded-feasibility-game-positive-t.md)
- [Every symmetric zero-sum game has a solution](every-symmetric-game-has-a-solution.md)

## Sources

- Ilan Adler, "The equivalence of linear programs and zero-sum games", International Journal of Game Theory 42(1), 165-177, 2013, Section 2 (the Dantzig game associated with $F(A, b)$ and Proposition 4) and Section 3.1 (Propositions 6 and 7, equation (8) and the bound $\hat\beta \le m(\sqrt{m}\,\theta)^m + 1$ for integer data).
