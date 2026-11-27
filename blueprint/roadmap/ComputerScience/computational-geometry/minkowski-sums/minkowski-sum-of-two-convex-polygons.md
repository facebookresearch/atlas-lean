# Minkowski sum of two convex polygons

The Minkowski sum of sets $A, B \subseteq \mathbb{R}^2$ is $A \oplus B = \{a + b : a \in A, b \in B\}$. For a direction $u$, the points of $A \oplus B$ extreme in direction $u$ are the sums of points of $A$ and of $B$ extreme in direction $u$. Consequently, if $P$ and $R$ are convex polygons with $n$ and $m$ edges, then $P \oplus R$ is a convex polygon with at most $n + m$ edges, whose edge vectors are those of $P$ and $R$ merged in cyclic order of their directed angles, co-directed vectors being added, and it can be computed in $O(n + m)$ time.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 34, "Computing the Minkowski Sum of Convex Polygons": the Observation on extreme points and the Claim ($O(n + m)$ time and at most $n + m$ edges)
