# Divide-and-conquer upper hull

Let $P$ be a set of $n$ points of $\mathbb{R}^2$ with distinct $x$-coordinates and no three on a line. The divide-and-conquer algorithm sorts $P$ by $x$-coordinate, splits it by a vertical line into two halves $P'$ and $P''$ of sizes $\lfloor n/2 \rfloor$ and $\lceil n/2 \rceil$, computes their upper hulls $H'$ and $H''$ recursively (by brute force when at most three points remain), and merges them along the upper tangent: the line through a vertex $p'$ of $H'$ and a vertex $p''$ of $H''$ with all of $P$ on or below it. Starting from the rightmost vertex of $H'$ and the leftmost vertex of $H''$, the tangent is found by advancing $p''$ while $\mathrm{Orient}(p', p'', q'') \ge 0$ for its successor $q''$ and retreating $p'$ while $\mathrm{Orient}(p'', p', q') \le 0$ for its predecessor $q'$, which takes $O(n)$ orientation tests; the merged upper hull keeps the vertices of $H'$ up to $p'$ and of $H''$ from $p''$. The algorithm returns the upper hull of $P$, and with the running time $T(n) = 2T(n/2) + O(n)$ of the recursion it takes $O(n \log n)$ time; the lower hull is symmetric.

## Depends on

- [Convex hull of a finite planar point set](convex-hull-of-a-finite-planar-point-set.md)
- [Direction of three points](../orientation-and-segment-intersection-tests/direction.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 2, "Convex Hull by Divide-and-Conquer" and "Computing the upper tangent"
