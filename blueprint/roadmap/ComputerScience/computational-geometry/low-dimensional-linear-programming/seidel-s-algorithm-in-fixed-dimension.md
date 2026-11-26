# Seidel's algorithm in fixed dimension

Let $h_1, \dots, h_n$ be closed halfspaces in $\mathbb{R}^d$ and $c \in \mathbb{R}^d$ an objective vector, and consider maximizing $c \cdot x$ over $h_1 \cap \dots \cap h_n$. Assume that the program restricted to $h_1, \dots, h_d$ has a unique optimal vertex, that every program on a subset containing $h_1, \dots, h_d$ is bounded, and that the constraints are in general position, so that every optimal vertex is the intersection of exactly $d$ bounding hyperplanes.

Seidel's randomized incremental algorithm inserts $h_{d+1}, \dots, h_n$ in uniformly random order; when the current optimum violates the new constraint $h_i$, it solves recursively the $(d-1)$-dimensional program obtained by intersecting the earlier constraints with the hyperplane bounding $h_i$ and projecting $c$ onto it, solving one-dimensional programs directly, and it reports infeasibility when a recursive program is infeasible. It solves the program in expected time $O(d! \, n)$, the constant not depending on $d$, the expectation being over the insertion order only.

## Depends on

- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)
- [Average formula for the expected time over random orderings](../../randomized-algorithms/average-case-running-time/expected-time-uniform-permutation.md)

## Proof depends on

- [A violated constraint contains the new optimum](a-violated-constraint-contains-the-new-optimum.md)

## Informally uses

- [Seidel's randomized algorithm for two-variable linear programming](../polygons-and-triangulations/seidel-s-randomized-incremental-algorithm-for.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 7, "Backwards Analysis for Randomized LP" and "Eliminating the Dependence on Dimension": $T_d(n) = O(d!\,n)$ with $p_i = d/i$
