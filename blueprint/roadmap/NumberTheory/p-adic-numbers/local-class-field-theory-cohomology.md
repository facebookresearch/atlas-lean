# Local class field theory: cohomology and the existence theorem

This node is still to be broken down. It covers the cohomological theory that constructs
[the local Artin map](local-class-field-theory.md) and the local existence theorem, which the global theory
also uses directly. Let $K$ be a local field of characteristic $0$ (a finite extension of $\mathbb{Q}_p$, or
$\mathbb{R}$ or $\mathbb{C}$) and $L/K$ a finite Galois extension with group $G$, of degree $n$; cohomology
of profinite groups is computed with continuous cochains, and $U_L$ denotes the unit group of the ring of
integers of a non-archimedean $L$. It contains the following statements, following Milne's Chapters I and
III.

1. **Unramified extensions.** If $K$ is non-archimedean and $L/K$ is unramified, then
   $\hat H^r(G, U_L) = 0$ for all $r \in \mathbb{Z}$, and $\mathrm{Nm}_{L/K}(U_L) = U_K$ (Milne,
   Propositions III.1.1 and III.1.2).
2. **The invariant map.** There is a canonical injective homomorphism
   $\mathrm{inv}_K \colon H^2(\mathrm{Gal}(\overline{K}/K), \overline{K}^\times) \to \mathbb{Q}/\mathbb{Z}$,
   an isomorphism for $K$ non-archimedean and with image $\tfrac12\mathbb{Z}/\mathbb{Z}$ for
   $K = \mathbb{R}$, such that $\mathrm{inv}_L \circ \mathrm{Res} = [L : K] \cdot \mathrm{inv}_K$; it
   identifies $H^2(G, L^\times)$ with the subgroup $\tfrac1n\mathbb{Z}/\mathbb{Z}$, and
   $H^1(G, L^\times) = 0$ (Milne, Theorem III.2.1, and Section VIII.4 for $\mathbb{R}$). For $L/K$
   cyclic, the Herbrand quotient of $L^\times$ is $h(L^\times) = n$, and $h(U_L) = 1$ when $K$ is
   non-archimedean (Milne, Lemma III.2.5; for $\mathbb{C}/\mathbb{R}$, $\hat H^0 = \mathbb{R}^\times / \mathbb{R}_{>0}$
   has order $2$ and $\hat H^{-1} = 0$).
3. **The local fundamental class.** For $K$ non-archimedean, the class $u_{L/K} \in H^2(G, L^\times)$ of
   invariant $1/n$ makes cup product an isomorphism $\hat H^r(G, \mathbb{Z}) \to \hat H^{r+2}(G, L^\times)$
   for all $r$ (Tate's theorem, Milne, Theorem II.3.11); for $r = -2$ this is an isomorphism
   $G^{\mathrm{ab}} \to K^\times / \mathrm{Nm}_{L/K}(L^\times)$ (Milne, Theorem III.3.1). For $L/K$ abelian
   its inverse $K^\times / \mathrm{Nm}_{L/K}(L^\times) \to G$ sends a uniformizer to the Frobenius element
   when $L/K$ is unramified (Milne, Proposition III.1.9 and Lemma III.3.7) and is compatible with
   restriction to subextensions (Milne, 3.3), so these inverses define a homomorphism
   $K^\times \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$ with the two properties of the local Artin map (Milne,
   Theorem III.3.4).
4. **The local existence theorem.** For $K$ non-archimedean, every open subgroup of finite index in
   $K^\times$ is a norm group $\mathrm{Nm}_{L/K}(L^\times)$ of a finite abelian extension, so
   $L \mapsto \mathrm{Nm}_{L/K}(L^\times)$ is an inclusion-reversing bijection between the finite abelian
   extensions of $K$ and the open subgroups of finite index (Milne, Theorem I.1.4, Corollaries I.1.2 and
   I.1.5, Theorem III.5.1). For every finite extension $L/K$, the norm group $\mathrm{Nm}_{L/K}(L^\times)$
   is open if it has finite index (Milne, Lemma I.1.3), and in characteristic $0$ every subgroup of finite
   index of $K^\times$ is open (Milne, 1.7).

A good expansion has a page for each numbered item. Items 1, 2 and 3 give the existence of the local
Artin map and item 4 its uniqueness (Milne, Theorem I.1.13). The properties of the local Artin map that
the global theory uses beyond its definition are in
[functoriality and explicit reciprocity](local-class-field-theory-functoriality.md).

## Depends on

- [Herbrand quotient](../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient.md), for the statements of item 2

## Proof depends on

- [Herbrand quotients agree across a map with finite kernel and cokernel](../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-finite-kernel-cokernel.md), for item 2
- [Periodicity of Tate cohomology for finite cyclic groups](../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md), for item 1
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for Tate's theorem and the inflation–restriction sequences in items 2 and 3
- [Index of the n-th powers in a local field of characteristic zero](index-of-n-th-powers.md), for the local existence theorem in item 4
- [The p-adic exponential on a neighbourhood of zero](p-adic-exponential.md), for an open subgroup of $U_L$ with trivial cohomology (Milne, Lemma III.2.4), in item 2

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Chapter I, Section 1 (Corollary 1.2, Lemma 1.3,
  Theorem 1.4, Corollary 1.5, 1.7, Theorem 1.13); Chapter II, Theorem 3.11 (Tate's theorem); Chapter III,
  Sections 1–3 and 5 (Propositions 1.1, 1.2 and 1.9, Theorem 2.1, Lemmas 2.4 and 2.5, Theorem 3.1, 3.3,
  Theorem 3.4, Lemma 3.7, Theorem 5.1); Section VIII.4 (the invariant map of $\mathbb{R}$).
