# Existence of constrained Delaunay triangulations

Let $P \subset \mathbb{R}^2$ be a finite set of at least three points, not all on one line, and $G = (P, E)$ a plane straight-line graph on $P$. A triangulation $T$ of $P$ *respects* $G$ if it contains every segment of $E$. A point $q \in P$ is *visible* from the interior of a triangle $\Delta$ if for some point $p$ in the interior of $\Delta$ the segment $pq$ meets no segment of $E$ except at $q$ (equivalently, the relative interior of $pq$ meets no segment of $E$). A triangulation $T$ of $P$ that respects $G$ is a *constrained Delaunay triangulation* of $P$ with respect to $G$ if, for every triangle $\Delta$ of $T$, every point of $P$ strictly inside the circumcircle of $\Delta$ is invisible from the interior of $\Delta$. For every such $P$ and every plane straight-line graph $G = (P, E)$ a constrained Delaunay triangulation exists.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 6 (Delaunay triangulations), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%206.pdf>: Section 6.7, the definition of a constrained Delaunay triangulation (respecting $G$, visibility blocked by the segments of $E$) and Theorem 6.21
