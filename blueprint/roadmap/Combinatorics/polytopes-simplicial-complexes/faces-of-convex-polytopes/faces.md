# Faces of a convex polytope

Let $s$ be a finite set of points in a real normed space $E$ (for example $\mathbb{R}^n$) and let
$P = \operatorname{conv} s$. A face of $P$ is either the empty set or a set of the form

$$F = \{x \in P : \ell(x) \ge \ell(y) \text{ for all } y \in P\}$$

for a continuous linear functional $\ell$ on $E$: the points where $\ell$ attains its maximum over
$P$. The zero functional gives $F = P$, so $P$ is a face of itself; the empty set is a face by
convention.

Using continuous functionals loses nothing in a normed space. Every linear functional on the
finite-dimensional span of $s$ is continuous and, by the Hahn–Banach theorem, extends to a
continuous linear functional on $E$ with the same values on $P$. So these are exactly the faces of
the standard definition: the intersections of $P$ with the hyperplane $\ell(x) = c$ of a valid inequality $\ell(x) \le c$ (taking $c = \max_P \ell$) for an arbitrary linear functional $\ell$. For polytopes, the exposed faces are also exactly the convex extreme subsets.

The normed-space hypothesis matters. On a vector space with a coarser topology the continuous dual
can be trivial, for instance $\mathbb{R}$ with the indiscrete topology. Only $\emptyset$ and $P$
would then be "faces" in this sense, so the definition is stated for normed spaces only.

## Sources

- G. M. Ziegler, *Lectures on Polytopes*, Graduate Texts in Mathematics 152, Springer (cited for terminology only, without theorem numbers; not consulted for this entry).
- G. M. Ziegler, "Face numbers of 4-polytopes and 3-spheres", Proceedings of the International Congress of Mathematicians, Beijing 2002, arXiv:math/0208073v2 (20 June 2003), Section 2. The arXiv version was read.
