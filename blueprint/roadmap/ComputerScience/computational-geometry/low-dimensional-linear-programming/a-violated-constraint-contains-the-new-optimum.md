# A violated constraint contains the new optimum

Let $h_1, \dots, h_n$ be closed halfspaces in $\mathbb{R}^d$ and $c \in \mathbb{R}^d$ an objective vector, and consider maximizing $c \cdot x$ over $h_1 \cap \dots \cap h_n$. Assume that every program on a subset of the constraints containing $h_1, \dots, h_d$ is bounded and, when feasible, has a unique optimal point, and that the constraints are in general position, so that this optimal point is a vertex lying on exactly $d$ of the bounding hyperplanes. (Uniqueness is needed: for maximizing $-x - y$ subject to $x, y \ge 0$ and $x + y \ge 2$ every point of a segment is optimal, although every vertex lies on exactly two constraint lines.)

Let $v_{i-1}$ be the unique optimal point for $h_1, \dots, h_{i-1}$ with $i > d$. If $v_{i-1} \notin h_i$ and the program for $h_1, \dots, h_i$ is feasible, then its optimal point lies on the hyperplane bounding $h_i$.

## Depends on

- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 7, the assumption that the optimal point is a unique vertex ("Feasible") and the lemma that if after the addition of $h_i$ the LP is still feasible but the optimum changes, the new optimum lies on the hyperplane bounding $h_i$
