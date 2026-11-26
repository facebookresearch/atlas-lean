# A violated constraint contains the new optimum

Let $h_1, \dots, h_n$ be closed halfspaces in $\mathbb{R}^d$ and $c \in \mathbb{R}^d$ an objective vector, and consider maximizing $c \cdot x$ over $h_1 \cap \dots \cap h_n$. Assume that the program restricted to $h_1, \dots, h_d$ has a unique optimal vertex, that every program on a subset containing $h_1, \dots, h_d$ is bounded, and that the constraints are in general position, so that every optimal vertex is the intersection of exactly $d$ bounding hyperplanes.

Let $v_{i-1}$ be the optimal vertex for $h_1, \dots, h_{i-1}$ with $i > d$. If $v_{i-1} \notin h_i$ and the program for $h_1, \dots, h_i$ is feasible, then its optimal vertex lies on the hyperplane bounding $h_i$.

## Depends on

- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 7, the lemma that if after the addition of $h_i$ the LP is still feasible but the optimum changes, the new optimum lies on the hyperplane bounding $h_i$
