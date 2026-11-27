# Seidel's algorithm in fixed dimension

Let $h_1, \dots, h_n$ be closed halfspaces in $\mathbb{R}^d$ and $c \in \mathbb{R}^d$ an objective vector, and consider maximizing $c \cdot x$ over $h_1 \cap \dots \cap h_n$. Assume that every program on a subset of the constraints containing $h_1, \dots, h_d$ is bounded and, when feasible, has a unique optimal point, and that the constraints are in general position, so that this optimal point is a vertex lying on exactly $d$ of the bounding hyperplanes. (Uniqueness is needed: for maximizing $-x - y$ subject to $x, y \ge 0$ and $x + y \ge 2$ every point of a segment is optimal, although every vertex lies on exactly two constraint lines.)

Seidel's randomized incremental algorithm inserts $h_{d+1}, \dots, h_n$ in uniformly random order; when the current optimum violates the new constraint $h_i$, it solves recursively the $(d-1)$-dimensional program obtained by intersecting the earlier constraints with the hyperplane bounding $h_i$ and projecting $c$ onto it, solving one-dimensional programs directly, and it reports infeasibility when a recursive program is infeasible. It solves the program in expected time $O(n)$ for every fixed $d$, the expectation being over the insertion order only. The proof is a backwards analysis: the probability that the program after the insertion of the $j$-th randomly ordered constraint is feasible and has a different optimum is at most $d/j$, since that optimum is defined by $d$ of the constraints and depends only on the set inserted so far. An insertion that makes the program infeasible may trigger the recursive call with probability $1$, but it ends the algorithm, so its single recursive call is charged separately.

## Depends on

- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)
- [Average formula for the expected time over random orderings](../../randomized-algorithms/average-case-running-time/expected-time-uniform-permutation.md)

## Proof depends on

- [A violated constraint contains the new optimum](a-violated-constraint-contains-the-new-optimum.md)
- [The optimum changes with probability at most d/i](the-optimum-changes-with-probability-at-most-d-over-i.md)

## Informally uses

- [Seidel's randomized algorithm for two-variable linear programming](../polygons-and-triangulations/seidel-s-randomized-incremental-algorithm-for.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 7, "Backwards Analysis for Randomized LP" and "Eliminating the Dependence on Dimension". For that calculation the notes treat all $i$ constraints, the first $d$ included, as randomly permuted, which gives $p_i = d/i$ and $T_d(n) = O(d!\,n)$; with the first $d$ constraints fixed, as in the algorithm stated here, the bound is $d/j$ for the $j$-th random constraint
