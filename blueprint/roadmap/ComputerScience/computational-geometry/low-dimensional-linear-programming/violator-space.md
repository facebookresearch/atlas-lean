# Violator space

A *violator space* is a pair $(H, \mathrm{cl})$ of a finite set $H$ of *constraints* and a map $\mathrm{cl} : 2^H \to 2^H$ such that
- *consistency*: $\mathrm{cl}(X) \cap X = \emptyset$ for all $X \subseteq H$;
- *locality*: for $X \subseteq Y \subseteq H$, if $\mathrm{cl}(X) \cap Y = \emptyset$ then $\mathrm{cl}(X) = \mathrm{cl}(Y)$;
- *monotonicity*: for $X \subseteq Y \subseteq Z \subseteq H$, if $\mathrm{cl}(X) = \mathrm{cl}(Z)$ then $\mathrm{cl}(X) = \mathrm{cl}(Y) = \mathrm{cl}(Z)$.

A constraint $f$ *violates* $X$ if $f \in \mathrm{cl}(X)$. A *basis* of $X$ is a set $B \subseteq X$ with $\mathrm{cl}(B) = \mathrm{cl}(X)$ such that $\mathrm{cl}(B') \ne \mathrm{cl}(B)$ for every proper subset $B' \subsetneq B$. The *combinatorial dimension* is the largest size of a basis. Violator spaces extend LP-type problems to settings without an objective function. For example, let $H$ be a set of segments in the plane in general position, and let the origin lie on no segment of $H$ and on no vertical line through an endpoint of a segment or a crossing point of two segments of $H$, so that for every $X \subseteq H$ it lies in the interior of a unique trapezoid of the vertical decomposition of the arrangement of $X$. Let $\mathrm{cl}(X)$ be the set of segments of $H$ that meet the interior of that trapezoid; this is a violator space whose bases have at most four segments.


## Related topics

- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Linear programming in low dimensions" (Chapter 22), <https://sarielhp.org/book/chapters/lp.pdf>: Section 22.6 introduction, Example 22.6.1 (the trapezoid containing the origin) and Definition 22.6.2 (violator space, basis, combinatorial dimension)
