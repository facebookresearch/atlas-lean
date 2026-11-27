# The closest pair is a Delaunay edge

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line and no four on a common circle, and let $p, q \in P$ be a closest pair. Then $pq$ is an edge of the Delaunay triangulation of $P$: the circle with diameter $pq$ contains no other point of $P$, since such a point would be closer to $p$ or to $q$ than they are to each other, so $pq$ has an empty circle through its endpoints.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)

## Proof depends on

- [Empty circle characterization of Delaunay edges](empty-circle-characterization-of-delaunay-edges.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, "Closest pair property" and its proof
