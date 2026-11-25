# Termination and correctness of the simplex method with Bland's rule

For a linear program in slack form, each pivot step of the simplex method preserves the set of feasible solutions and the objective function. With Bland's rule (choose the entering and leaving variables of smallest index among the eligible ones) the simplex method never cycles and therefore terminates. Together with a first phase that decides feasibility and finds an initial basic feasible solution, it either reports that the program is infeasible, reports that it is unbounded, or returns an optimal basic feasible solution whose final tableau certifies optimality.

## Proof depends on

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 4th ed., MIT Press, 2022
- R. G. Bland, "New finite pivoting rules for the simplex method", *Mathematics of Operations Research* 2(2):103–107, 1977
