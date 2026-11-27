# Chan's output-sensitive convex hull algorithm

Let $P$ be a set of $n \ge 3$ points of $\mathbb{R}^2$ with no three on a line, and let $h$ be the number of vertices of $\operatorname{conv}(P)$. Chan's algorithm runs, for $h^* = 2^{2^i}$ with $i = 1, 2, \dots$ (capped at $n$), a conditional hull computation: partition $P$ arbitrarily into $\lceil n/h^* \rceil$ groups of at most $h^*$ points, compute the hull of each group in $O(h^* \log h^*)$ time, then run Jarvis's march for at most $h^*$ steps. In each step, with current vertex $p$, every group other than $\{p\}$ offers one candidate (a group consisting of $p$ alone offers none): for the group containing $p$, the successor of $p$ in counterclockwise order on that group's hull; for a group with at most two points, the point found directly; and for any other group, the vertex where the supporting line from $p$ touches its hull with the hull on its left, which exists because $p$, a vertex of $\operatorname{conv}(P)$, lies outside the hull of a group that does not contain it, and is found in $O(\log h^*)$ time. The march moves to the candidate with the least turn; the run succeeds once the march closes within $h^*$ steps. The algorithm outputs the vertices of $\operatorname{conv}(P)$ in counterclockwise order in $O(n \log h)$ time.

## Depends on

- [Convex hull of a finite planar point set](convex-hull-of-a-finite-planar-point-set.md)

## Proof depends on

- [Jarvis's march](jarvis-s-march.md)
- [Tangents from an external point to a convex polygon](tangents-from-an-external-point-to-a-convex-polygon.md)
- [The computed convex hull equals the convex hull](../monotone-chain-convex-hull-algorithm/the-computed-convex-hull-equals-the-convex-hull.md)
- [Chan's conditional hull step](chan-s-conditional-hull-step.md)

## Sources

- T. M. Chan, "Optimal output-sensitive convex hull algorithms in two and three dimensions", *Discrete & Computational Geometry* 16 (1996), 361–368, <https://doi.org/10.1007/BF02712873>: Section 2, Algorithm Hull2D$(P, m, H)$ (groups of size at most $m$, Graham's scan on each group, wrapping steps by binary search on each group hull, time $O(n(1 + H/m) \log m)$) and Algorithm Hull2D$(P)$ with $m = H = \min\{2^{2^t}, n\}$, for $O(n \log h)$ time
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, "Chan's Algorithm": the conditional hull with mini-hulls and the supporting-line lemma, the squaring search $h^* = 2^{2^i}$ and the total time $O(n \log h)$
