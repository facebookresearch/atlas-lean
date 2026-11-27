# Divide-and-conquer upper hull

Let $P$ be a set of $n$ points of $\mathbb{R}^2$ with distinct $x$-coordinates and no three on a line. The divide-and-conquer algorithm sorts $P$ by $x$-coordinate, splits it by a vertical line into two halves $P'$ and $P''$ of sizes $\lfloor n/2 \rfloor$ and $\lceil n/2 \rceil$, computes their upper hulls $H'$ and $H''$ recursively (by brute force when at most three points remain; the upper hull of one or two points is the list of these points by increasing $x$-coordinate), and merges them along the upper tangent: the line through a vertex $p'$ of $H'$ and a vertex $p''$ of $H''$ with all of $P$ on or below it. Write $\mathrm{Orient}(p, q, r) = -\mathrm{DIRECTION}(p, q, r)$, which is positive when $p, q, r$ make a counterclockwise (left) turn. Starting from the rightmost vertex $p'$ of $H'$ and the leftmost vertex $p''$ of $H''$, the tangent is found by repeating, until neither $p'$ nor $p''$ moves, the two walks: advance $p''$ while $\mathrm{Orient}(p', p'', q'') \ge 0$ for its successor $q''$, then retreat $p'$ while $\mathrm{Orient}(p'', p', q') \le 0$ for its predecessor $q'$. One pass is not enough: for the halves $\{(0,4), (1,0)\}$ and $\{(2,0), (3,-1)\}$ the first walk does not move, the second moves $p'$ to $(0,4)$, and only then can $p''$ advance to $(3,-1)$. This takes $O(n)$ orientation tests in total; the merged upper hull keeps the vertices of $H'$ up to $p'$ and of $H''$ from $p''$. The algorithm returns the upper hull of $P$, and with the running time $T(n) = 2T(n/2) + O(n)$ of the recursion it takes $O(n \log n)$ time; the lower hull is symmetric.

## Depends on

- [Convex hull of a finite planar point set](convex-hull-of-a-finite-planar-point-set.md)
- [Direction of three points](../orientation-and-segment-intersection-tests/direction.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 2, "Convex Hull by Divide-and-Conquer" and "Computing the upper tangent" (procedure UpperTangent, which repeats both walks until neither condition holds; its Orient is positive for counterclockwise turns)
