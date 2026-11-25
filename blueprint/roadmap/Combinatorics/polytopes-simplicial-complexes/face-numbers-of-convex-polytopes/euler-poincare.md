# Euler–Poincaré relation

Let $s$ be a nonempty finite set of points in $\mathbb{R}^n$ and let $P = \operatorname{conv} s$
have dimension $d$. Then

$$\sum_{k=0}^{d} (-1)^k f_k(P) = f_0 - f_1 + f_2 - \cdots + (-1)^d f_d = 1,$$

where $f_d = 1$ counts $P$ itself. Moving $f_d$ to the right gives the form in Ziegler's ICM
report,

$$f_0 - f_1 + \cdots + (-1)^{d-1} f_{d-1} = 1 + (-1)^{d-1},$$

and adding $f_{-1} = 1$ for the empty face gives $\sum_{k=-1}^{d} (-1)^k f_k = 0$. For $d = 3$ this
is Euler's equation $f_0 - f_1 + f_2 = 2$, and for $d = 4$ it reads $f_0 - f_1 + f_2 - f_3 = 0$.

The polytope need not be full-dimensional in $\mathbb{R}^n$: $d$ is the dimension of its affine
hull. The hypothesis $s \ne \emptyset$ is needed, since the empty polytope has no nonempty faces
and the sum is then $0$. Examples: a segment has $f_0 = 2$, $f_1 = 1$ and
$2 - 1 = 1$; a triangle has $3 - 3 + 1 = 1$.

## Background

- [Euler's polyhedron formula](../../../Geometry/discrete-geometry/part-01/euler-polyhedron-formula.md):
  the case $d = 3$, stated there for an arbitrary polygonal cellulation of the boundary of a
  3-polytope rather than for its face lattice.

## Sources

- G. M. Ziegler, "Face numbers of 4-polytopes and 3-spheres", Proceedings of the International Congress of Mathematicians, Beijing 2002, arXiv:math/0208073v2 (20 June 2003), Section 2. The arXiv version was read.
- G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City Mathematics Series, Volume 14 (2004), arXiv:math/0411400v2 (7 December 2005). Numbering as in this arXiv version, which is the version read; the published version was not consulted. Section 1.1 (the case $d = 3$, taken for granted there) and Lecture 4 (the case $d = 4$).
