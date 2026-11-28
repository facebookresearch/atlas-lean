# The Brauer group of a local field embeds in the second cohomology of the functions on a torsor with a point

Let $k$ be a field of characteristic $0$ with algebraic closure $\bar k$, $G_k = \operatorname{Gal}(\bar k/k)$, and $Y$ a smooth,
geometrically integral variety over $k$ with $Y(k) \ne \varnothing$, such as a principal homogeneous space of an
[abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over a local field $k$ that has a
$k$-point. Then the map

$$\mathrm{Br}(k) = H^2(G_k, \bar k^\times) \to H^2(G_k, \bar k(Y)^\times)$$

induced by the inclusion of the constants $\bar k^\times \subseteq \bar k(Y)^\times$ is injective.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the injectivity of $\mathrm{Br}(Y) \to \mathrm{Br}(k(Y))$ for a smooth variety $Y$ (Milne cites Milne 1980, II 2.6);
- the section of $\mathrm{Br}(k) \to \mathrm{Br}(Y)$ given by a point of $Y(k)$, which makes this map injective;
- the comparison of $H^2(G_k, \bar k(Y)^\times)$ with the kernel of $\mathrm{Br}(k(Y)) \to \mathrm{Br}(\bar k(Y))$, which turns these into the
  statement, as in Milne's diagram.

## Depends on

- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for Galois cohomology

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Remark 6.11, p. 80 ("The zero at lower left is a consequence of the local triviality of $X$. Indeed,
  consider an arbitrary smooth variety $Y$ over a field $k$. The map $\mathrm{Br}(Y) \to \mathrm{Br}(k(Y))$ is injective (Milne 1980,
  II 2.6). The structure map $Y \to \operatorname{Spec}(k)$ induces a map $\mathrm{Br}(k) \to \mathrm{Br}(Y)$, and any element of $Y(k)$ defines
  a section to this map, which is then injective", and the diagram after it).
- J. S. Milne, *Étale Cohomology*, Princeton University Press, 1980, Chapter II, 2.6, as cited by Milne, *Arithmetic
  Duality Theorems*, p. 80; not read.
