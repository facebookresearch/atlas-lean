# The boundary complex of a simplicial polytope is a simplicial sphere

Let $s$ be a finite set in $\mathbb{R}^d$ whose convex hull $P$ has nonempty interior (so $P$ is a
$d$-polytope) and is simplicial. Then there is a finite simplicial $(d-1)$-sphere $X$ in
$\mathbb{R}^d$, (a finite geometric simplicial complex in $\mathbb{R}^d$ whose underlying space is homeomorphic to the unit sphere $S^{d-1}$) with the same face numbers:
$f_k(X) = f_k(P)$ for every $k < d$.

The intended $X$ is the boundary complex of $P$: its simplices are the proper faces of $P$, and
radial projection from an interior point maps its underlying space, the boundary of $P$,
homeomorphically onto a sphere. Combined with the Dehn–Sommerville equations for simplicial
spheres, this gives the Dehn–Sommerville equations $h_k(P) = h_{d-k}(P)$ for simplicial
$d$-polytopes, where $h$ is computed from $(f_{-1}, f_0, \dots, f_{d-1})$ by the same
formula.

Degenerate case $d = 0$: $\mathbb{R}^0$ is a point, the unit sphere in it is empty, and the empty
complex works; there is no $k < 0$ to check.

## Background

- [Dehn–Sommerville equations](../face-numbers-of-simplicial-spheres/dehn-sommerville.md): the
  symmetry of the h-vector of a simplicial sphere, which this statement transfers to simplicial
  polytopes.
- [Finite simplicial sphere](../face-numbers-of-simplicial-spheres/finite-simplicial-sphere.md):
  the class of complexes in which $X$ is sought.
- [Simplicial polytope](../faces-of-convex-polytopes/is-simplicial.md): the hypothesis on $P$.

## Sources

- G. M. Ziegler, "Face numbers of 4-polytopes and 3-spheres", Proceedings of the International Congress of Mathematicians, Beijing 2002, arXiv:math/0208073v2 (20 June 2003), Sections 2 and 3 (boundary complexes of polytopes as strongly regular cellulations of spheres, Section 3). The arXiv version was read.
