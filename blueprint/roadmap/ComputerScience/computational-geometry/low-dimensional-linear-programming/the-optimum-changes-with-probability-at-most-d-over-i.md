# The optimum changes with probability at most d/i

Let $h_1, \dots, h_n$ be closed halfspaces in $\mathbb{R}^d$ and $c$ an objective vector such that every program of maximizing $c \cdot x$ over a subset of the constraints containing $h_1, \dots, h_d$ is bounded and, when feasible, has a unique optimal point, which lies on exactly $d$ of the bounding hyperplanes. Seidel's algorithm keeps $h_1, \dots, h_d$ first and inserts $h_{d+1}, \dots, h_n$ in uniformly random order. For $1 \le i \le n - d$, let $p_i$ be the probability that the program after the $i$-th randomly ordered constraint is feasible and its optimal point differs from the one before that insertion. Then $p_i \le d/i$. Indeed the optimal point after the insertion depends only on the set of constraints inserted so far, it lies on exactly $d$ bounding hyperplanes, and it differs from the previous one only if one of these $d$ constraints was the last inserted; at most $d$ of them are among the $i$ randomly ordered constraints, each of which is the last with probability $1/i$.

## Depends on

- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)
- [Uniformly random rearrangement of a list](../../randomized-algorithms/average-case-running-time/uniform-permutation.md)


## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 7, "Backwards Analysis for Randomized LP": the optimum changes if and only if one of the $d$ defining halfspaces was the last inserted, so $p_i = d/i$
