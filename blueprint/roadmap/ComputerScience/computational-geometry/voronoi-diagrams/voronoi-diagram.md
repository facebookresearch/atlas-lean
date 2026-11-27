# Voronoi diagram of a planar point set

Let $P = \{p_1, \dots, p_n\}$ be a set of $n \ge 2$ distinct points (*sites*) in $\mathbb{R}^2$. The *Voronoi cell* of $p_i$ is

$$V(p_i) = \{q \in \mathbb{R}^2 : \|q - p_i\| \le \|q - p_j\| \text{ for all } j\},$$

the intersection of the $n - 1$ closed half-planes $\{q : \|q - p_i\| \le \|q - p_j\|\}$ bounded by the perpendicular bisectors of $p_i p_j$, hence a convex, possibly unbounded, polygon. A point $q$ has as its *nearest sites* the sites at least distance from it. The *Voronoi diagram* $\mathrm{Vor}(P)$ is the subdivision of the plane into the $n$ cells: its *vertices* are the points with at least three nearest sites, and its *edges* are the maximal connected sets of points with exactly two nearest sites, which are relatively open segments, rays or lines; the closure of an edge, its *closed edge*, adds its endpoints, which are vertices. The cells here are closed; the cited notes define open cells (strict inequalities) and take closures for the diagram.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 11, the definition of the Voronoi cell as an intersection of bisector half-planes and of the Voronoi diagram
- F. Aurenhammer, "Voronoi diagrams — a survey of a fundamental geometric data structure", *ACM Computing Surveys* 23(3), 1991, p. 347: the region count, the unbounded regions of sites on the convex hull boundary, and the bounds on edges and vertices from Euler's relation
