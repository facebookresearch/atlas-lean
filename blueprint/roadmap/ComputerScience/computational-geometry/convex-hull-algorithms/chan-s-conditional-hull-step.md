# Chan's conditional hull step

Let $P$ be a set of $n$ points in $\mathbb{R}^2$ with no three on a line, $h$ the number of vertices of $\operatorname{conv}(P)$, and $h^* \ge 1$ a guess. The conditional hull step partitions $P$ into $\lceil n/h^* \rceil$ groups of at most $h^*$ points, computes the hull of each group by Graham's scan, and then runs at most $h^*$ steps of Jarvis's march, finding in each step the supporting line from the current vertex to each group hull by binary search. It runs in $O(n \log h^*)$ time; if $h \le h^*$ it returns the vertices of $\operatorname{conv}(P)$ in order, and otherwise it reports failure. Trying $h^* = 2^{2^i}$ for $i = 1, 2, \dots$ (capped at $n$) succeeds by $i = \lceil \log_2 \log_2 h \rceil$, and the total time $\sum_{i} O(n 2^i)$ is $O(n \log h)$.

## Depends on

- [Convex hull of a finite planar point set](convex-hull-of-a-finite-planar-point-set.md)

## Proof depends on

- [Tangents from an external point to a convex polygon](tangents-from-an-external-point-to-a-convex-polygon.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, "The Conditional Algorithm" (ConditionalHull$(P, h^*)$), the supporting-line lemma, and the analysis of repeated squaring of the guess
