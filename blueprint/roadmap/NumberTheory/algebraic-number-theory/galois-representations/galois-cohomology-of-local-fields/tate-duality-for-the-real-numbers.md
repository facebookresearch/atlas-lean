# Tate duality for the real numbers

Let $G = \operatorname{Gal}(\mathbb{C}/\mathbb{R})$, let $A$ be a finitely generated $G$-module and
$A' = \operatorname{Hom}(A, \mathbb{C}^\times)$, with $G$ acting by $(\sigma f)(a) = \sigma(f(\sigma^{-1} a))$.
Then $H^2(G, \mathbb{C}^\times) \cong \tfrac12 \mathbb{Z}/\mathbb{Z}$, and for every $i \in \mathbb{Z}$ the cup
product of Tate cohomology groups

$$\hat H^i(G, A') \times \hat H^{2-i}(G, A) \xrightarrow{\ \cup\ } H^2(G, \mathbb{C}^\times)$$

induces an isomorphism $\hat H^i(G, A') \to \hat H^{2-i}(G, A)^* = \operatorname{Hom}(\hat H^{2-i}(G, A), \mathbb{Q}/\mathbb{Z})$.
All these groups are finite and killed by $2$.

## Depends on

- [Cup products in Tate cohomology](../../../../RepresentationTheory/group-cohomology/cup-products-in-tate-cohomology.md), for cup products, here of a finite group in Tate cohomology

## Proof depends on

- [Periodicity of Tate cohomology for finite cyclic groups](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md)
- [The long exact Tate cohomology sequence of a finite group](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/long-exact-tate-cohomology-sequence-of-a-finite-group.md), for the long exact sequences of Tate cohomology, which reduce the theorem to $A = \mathbb{Z}/2\mathbb{Z}$, $\mathbb{Z}$ and $\mathbb{Z}(1)$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (7.2.17) Theorem and its proof,
  pp. 390–391.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 2.13 (a).
