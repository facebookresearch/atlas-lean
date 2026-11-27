# The Dantzig game of a bounded feasibility problem has no solution with t = 0

Over every linearly ordered field, for all $A \in K^{m\times n}$, $b \in K^m$ and $\beta \in K$, every solution $(y, v, x, u, t)$ of the Dantzig game associated with the bounded problem $F(\hat A, \hat b(\beta))$ ($Ax = b$, $\sum_j x_j + s = \beta$, $x, s \ge 0$) has $t > 0$.

## Proof sketch

A solution with $t = 0$ would give a nonzero nonnegative solution of the homogeneous system of the bounded problem. The added row forces $\sum_j x_j + s = 0$ for such a vector, so with $x, s \ge 0$ it would vanish, a contradiction.

## Depends on

- [Adler's Dantzig game of a linear feasibility problem](adler-feasibility-game.md)

## Proof depends on

- [Reading a linear program off a solution of Dantzig's game](dantzig-game-lp-readoff.md)

## Sources

- Ilan Adler, "The equivalence of linear programs and zero-sum games", International Journal of Game Theory 42(1), 165-177, 2013.
