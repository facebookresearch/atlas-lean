# Violator space

A *violator space* is a pair $(H, \mathrm{cl})$ of a finite set $H$ of *constraints* and a map $\mathrm{cl} : 2^H \to 2^H$ such that
- *consistency*: $\mathrm{cl}(X) \cap X = \emptyset$ for all $X \subseteq H$;
- *locality*: for $X \subseteq Y \subseteq H$, if $\mathrm{cl}(X) \cap Y = \emptyset$ then $\mathrm{cl}(X) = \mathrm{cl}(Y)$;
- *monotonicity*: for $X \subseteq Y \subseteq Z \subseteq H$, if $\mathrm{cl}(X) = \mathrm{cl}(Z)$ then $\mathrm{cl}(X) = \mathrm{cl}(Y) = \mathrm{cl}(Z)$.

A constraint $f$ *violates* $X$ if $f \in \mathrm{cl}(X)$. A *basis* of $X$ is a set $B \subseteq X$ with $\mathrm{cl}(B) = \mathrm{cl}(X)$ such that $\mathrm{cl}(B') \ne \mathrm{cl}(B)$ for every proper subset $B' \subsetneq B$. The *combinatorial dimension* is the largest size of a basis. Linear programs in $\mathbb{R}^d$ in general position, with $\mathrm{cl}(X)$ the set of constraints violated by the optimum of $X$, form violator spaces of combinatorial dimension $d$.

## Informally uses

- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Linear programming in low dimensions" (Chapter 22), <https://sarielhp.org/book/chapters/lp.pdf>: Definition 22.6.2 (violator space, basis, combinatorial dimension) and Definition 22.6.3
