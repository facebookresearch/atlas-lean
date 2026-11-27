# Seidel's randomized algorithm for two-variable linear programming

Consider a linear program in two variables with $n$ constraints. Include fixed bounding constraints $-M \le x \le M$ and $-M \le y \le M$, inserted first, so that every subset of constraints containing them has a compact, possibly empty, feasible region; and break ties by taking, among the optimal points, the lexicographically smallest one, which exists on a nonempty compact convex polygon and is unique. Seidel's algorithm inserts the remaining constraints in uniformly random order, maintains the optimum of the constraints inserted so far, and, when a new constraint violates the current optimum, recomputes the optimum on the boundary line of that constraint by a one-dimensional linear program over the constraints inserted so far in $O(i)$ time, reporting infeasibility if that one-dimensional program is infeasible. By backwards analysis the $i$-th inserted constraint changes the optimum with probability at most $2/i$, so the expected running time is $O(n)$.

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
