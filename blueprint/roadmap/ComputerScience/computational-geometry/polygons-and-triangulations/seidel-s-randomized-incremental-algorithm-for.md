# Seidel's randomized algorithm for two-variable linear programming

Consider a linear program in two variables with $n$ constraints whose objective is bounded below on the feasible region, which is ensured by including two fixed bounding constraints that are inserted first, and assume a fixed tie-breaking rule that makes the optimum of every subset of constraints containing the bounding constraints unique (for example, the lexicographically smallest optimal point). Seidel's algorithm inserts the remaining constraints in uniformly random order, maintains the optimum of the constraints inserted so far, and, when a new constraint violates the current optimum, recomputes the optimum on the boundary line of that constraint by a one-dimensional linear program over the constraints inserted so far in $O(i)$ time, reporting infeasibility if that one-dimensional program is infeasible. By backwards analysis the $i$-th inserted constraint changes the optimum with probability at most $2/i$, so the expected running time is $O(n)$.

## Depends on

- [Expected running time](../../randomized-algorithms/average-case-running-time/expected-time.md)

## Proof depends on

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- R. Seidel, "Small-dimensional linear programming and convex hulls made easy", *Discrete and Computational Geometry* 6(3):423–434, 1991
- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
