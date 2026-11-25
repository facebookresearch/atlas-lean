# Orthogonal range reporting in a kd-tree

Let $P$ be a set of $n$ points in the plane in general position, meaning no two share a coordinate. A [kd-tree](kd-tree.md) for $P$ splits at the median $x$-coordinate, then recursively at the median $y$-coordinate in each half, alternating axes. Each node corresponds to a rectangular region, and each leaf to one point.

**Theorem.**
1. The kd-tree uses $O(n)$ space and can be built in $O(n\log n)$ time.
2. Reporting the $k$ points of $P$ inside an axis-parallel query rectangle takes $O(\sqrt n + k)$ time.

**Proof.**
1. Median finding takes linear time and both recursive calls are on half the points, so $P(n) \le 2P(n/2) + O(n)$.
2. The query recurses only into regions that meet the rectangle, and it reports whole subtrees whose regions lie inside the rectangle. Its time is proportional to $k$ plus the number of visited regions crossed by an edge of the rectangle. A horizontal line crosses the regions of the root and its two children, but only two of the four grandchildren, each holding about $n/4$ points. So the number $\varphi(n)$ of regions it crosses satisfies $\varphi(n) = 2\varphi(n/4) + 3 = O(\sqrt n)$. The same holds for vertical lines, and the rectangle has four edges.

## Depends on

- [Kd-trees](kd-tree.md)

## Background

- [Orthogonal range reporting with range trees](../range-tree/orthogonal-range-reporting-with-range-trees.md)

## Sources

- P. K. Agarwal, *CPS234 Computational Geometry*, Lecture 8 "Orthogonal range searching" (scribe notes, 22 September 2005), Duke University, <https://courses.cs.duke.edu/cps234/fall05/notes/lecture08.pdf>: Section 8.3, covering construction by alternating medians, preprocessing $P(n) = O(n\lg n)$, Claims 3 and 4 (query time is proportional to the black and gray nodes, and there are at most $k$ black nodes), the recurrence $\varphi(n) = 2\varphi(n/4) + 3 = O(\sqrt n)$, the query time $O(\sqrt n + k)$, and space $O(n)$.
