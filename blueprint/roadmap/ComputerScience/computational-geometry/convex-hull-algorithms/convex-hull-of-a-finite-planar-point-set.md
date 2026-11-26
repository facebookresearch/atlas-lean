# Convex hull of a finite planar point set

Let $P$ be a finite set of $n \ge 3$ points of $\mathbb{R}^2$, not all on one line. Its convex hull $\operatorname{conv}(P)$, the set of convex combinations of points of $P$, is a convex polygon. A point $p \in P$ is a *vertex* of $\operatorname{conv}(P)$ if $p \notin \operatorname{conv}(P \setminus \{p\})$; write $h$ for the number of vertices. The *planar convex hull problem* takes $P$ as a list of coordinate pairs and asks for the vertices of $\operatorname{conv}(P)$ in counterclockwise order around its boundary; points of $P$ on the boundary that are not vertices are not reported.

Let $a$ be the lexicographically smallest vertex (least $x$-coordinate, and among those the least $y$-coordinate) and $b$ the lexicographically largest (greatest $x$-coordinate, and among those the greatest $y$-coordinate). The boundary of $\operatorname{conv}(P)$ splits at $a$ and $b$ into two chains: the *upper hull*, the chain of vertices traversed clockwise from $a$ to $b$, which lies on or above the segment $ab$, and the *lower hull*, traversed counterclockwise from $a$ to $b$. A vertical boundary edge at the left end therefore belongs to the upper hull, and one at the right end to the lower hull; when no two vertices share an $x$-coordinate, $a$ and $b$ are the leftmost and rightmost vertices.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 2, the planar convex hull problem (counterclockwise enumeration of the hull vertices) and the upper and lower hulls
