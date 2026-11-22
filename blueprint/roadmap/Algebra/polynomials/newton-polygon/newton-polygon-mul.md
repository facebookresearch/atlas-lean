# Ostrowski's theorem in the plane

For bivariate polynomials `f` and `g` over a commutative ring without zero divisors, the Newton polygon of the product is the Minkowski sum of the Newton polygons: `New(f g) = New(f) + New(g)`.

Multiplying polynomials thus adds their Newton polygons, which is why Minkowski sums and mixed areas govern the number of solutions of sparse polynomial systems. Every exponent of `f g` is a sum of an exponent of `f` and one of `g`, which gives `⊆`. Conversely, a vertex of `New(f) + New(g)` decomposes in only one way as such a sum, so the coefficient of `f g` there is a single nonzero product; and a polygon is the convex hull of its vertices. Over a ring with zero divisors the inclusion `⊆` still holds but equality can fail.

## Background

- [Mixed area](../../../AlgebraicGeometry/varieties-and-projective-geometry/bernstein-s-theorem-on-sparse-polynomial-systems/mixed-area.md): the Minkowski sums of Newton polygons that this theorem realizes as Newton polygons of products are what Bernstein's count measures.

## Sources

- B. Sturmfels, *Solving Systems of Polynomial Equations*, CBMS Regional Conference Series in Mathematics 97, AMS, 2002, Section 3.1.
- A. Ostrowski, *Über die Bedeutung der Theorie der konvexen Polyeder für die formale Algebra*, Jahresbericht der Deutschen Mathematiker-Vereinigung 30 (1921).
