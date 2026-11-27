# Chan's conditional hull step

Let $P$ be a set of $n$ points in $\mathbb{R}^2$ with no three on a line, $h$ the number of vertices of $\operatorname{conv}(P)$, and $h^* \ge 1$ a guess. The conditional hull step partitions $P$ into $\lceil n/h^* \rceil$ groups of at most $h^*$ points, computes the hull of each group in $O(h^* \log h^*)$ time (by Graham's scan or the monotone chain algorithm), and then runs at most $h^*$ steps of Jarvis's march. In each step, with current vertex $p$, every group other than $\{p\}$ offers one candidate (a group consisting of $p$ alone offers none): for the group containing $p$, the successor of $p$ in counterclockwise order on that group's hull; for a group with at most two points, the point found directly; and for any other group, the vertex where the supporting line from $p$ touches its hull with the hull on its left, found by binary search, which applies because $p$, a vertex of $\operatorname{conv}(P)$, lies outside the hull of a group that does not contain it. The march moves to the candidate with the least turn. It runs in $O(n \log h^*)$ time; if $h \le h^*$ it returns the vertices of $\operatorname{conv}(P)$ in order, and otherwise it reports failure. Trying $h^* = 2^{2^i}$ for $i = 1, 2, \dots$ (capped at $n$) succeeds by $i = \lceil \log_2 \log_2 h \rceil$, and the total time $\sum_{i} O(n 2^i)$ is $O(n \log h)$.

## Depends on

- [Convex hull of a finite planar point set](convex-hull-of-a-finite-planar-point-set.md)

## Proof depends on

- [Tangents from an external point to a convex polygon](tangents-from-an-external-point-to-a-convex-polygon.md)
- [Jarvis's march](jarvis-s-march.md)
- [The computed convex hull equals the convex hull](../monotone-chain-convex-hull-algorithm/the-computed-convex-hull-equals-the-convex-hull.md)

## Sources

- T. M. Chan, "Optimal output-sensitive convex hull algorithms in two and three dimensions", *Discrete & Computational Geometry* 16 (1996), 361–368, <https://doi.org/10.1007/BF02712873>: Section 2, Algorithm Hull2D$(P, m, H)$: groups of size at most $m$, Graham's scan on each group, at most $H$ wrapping steps by binary search on each group hull, time $O(n(1 + H/m) \log m)$, returning the hull when $H \ge h$ and "incomplete" otherwise
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, "The Conditional Algorithm" (ConditionalHull$(P, h^*)$), the supporting-line lemma, and the analysis of repeated squaring of the guess
