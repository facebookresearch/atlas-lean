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
3. **The local fundamental class and the cup-product formula.** For $K$ non-archimedean, the class
   $u_{L/K} \in H^2(G, L^\times)$ of invariant $1/n$ makes cup product an isomorphism
   $\hat H^r(G, \mathbb{Z}) \to \hat H^{r+2}(G, L^\times)$ for all $r$ (Tate's theorem, Milne, Theorem
   II.3.11); for $r = -2$ this is an isomorphism $G^{\mathrm{ab}} \to K^\times / \mathrm{Nm}_{L/K}(L^\times)$
   (Milne, Theorem III.3.1), whose inverse $\mathrm{rec}_{L/K}$ is the local Artin map of $L/K$. For $L/K$
   abelian, every $\chi \in \mathrm{Hom}(G, \mathbb{Q}/\mathbb{Z})$ and every $a \in K^\times$,

    $$\chi(\mathrm{rec}_{L/K}(a)) = \mathrm{inv}_K(a \cup \delta\chi),$$

    where $\delta \colon H^1(G, \mathbb{Q}/\mathbb{Z}) \to H^2(G, \mathbb{Z})$ is the connecting map of
    $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$ and $a \cup \delta\chi \in H^2(G, L^\times)$
    (Milne, Proposition III.3.6, which refers to Serre for the proof). The formula also holds for
    $\mathbb{C}/\mathbb{R}$, with $\mathrm{rec}_{\mathbb{C}/\mathbb{R}} \colon \mathbb{R}^\times / \mathbb{R}_{>0} \to \mathrm{Gal}(\mathbb{C}/\mathbb{R})$
    the isomorphism (Milne, 1.6 of Chapter I): for the nontrivial character $\chi$, cup product with
    $\delta\chi$ is the periodicity isomorphism $\hat H^0(G, \mathbb{C}^\times) \to H^2(G, \mathbb{C}^\times)$
    (Milne, Remark II.3.5), so $a = -1$ gives the element of order $2$ of $\mathrm{Br}(\mathbb{R})$, of
    invariant $1/2 = \chi(\mathrm{rec}_{\mathbb{C}/\mathbb{R}}(-1))$, and $a > 0$ gives $0$; for $L = K$, in
    particular at a complex place, both sides vanish. Since the right side does not change when a character
    of a quotient $\mathrm{Gal}(E/K)$ is inflated to $G$, the formula makes the maps $\mathrm{rec}_{L/K}$
    for abelian $L$ compatible with restriction to subextensions (Milne, 3.3, for which Milne's footnote 3
    says that the argument given there does not appear to be correct and that the statement follows from
    Proposition III.3.6); and for $L/K$ unramified it gives
    $\mathrm{rec}_{L/K}(a) = \mathrm{Frob}^{\mathrm{ord}_K(a)}$ (Milne, Lemma III.3.7; also Proposition
    III.1.9). So these maps define a homomorphism $K^\times \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$ with the two
    properties of the local Artin map (Milne, Theorem III.3.4).

4. **The local existence theorem.** For $K$ non-archimedean, every open subgroup of finite index in
   $K^\times$ is a norm group $\mathrm{Nm}_{L/K}(L^\times)$ of a finite abelian extension, so
   $L \mapsto \mathrm{Nm}_{L/K}(L^\times)$ is an inclusion-reversing bijection between the finite abelian
   extensions of $K$ and the open subgroups of finite index (Milne, Theorem I.1.4, Corollaries I.1.2 and
   I.1.5, Theorem III.5.1). Milne's proof, for characteristic $0$, rests on the following statement: if $K$
   contains a primitive $n$-th root of unity, an element of $K^\times$ that is a norm from every cyclic
   extension of $K$ of degree dividing $n$ is an $n$-th power (Milne, Proposition III.4.1). It follows from
   the Hilbert symbol $(a, b) \in \mu_n$, defined by cup product from the invariant map: the symbol is
   nondegenerate on $K^\times / K^{\times n}$, by the cup-product formula of item 3 and the density of the
   image of the local Artin map, and $(a, b) = 1$ if and only if $b$ is a norm from $K[a^{1/n}]$ (Milne,
   Proposition III.4.3 and Theorem III.4.4(c), (d)). The proof also uses the local norm limitation
   theorem: for every finite extension $L/K$, with $E$ the largest abelian extension of $K$ in $L$,
   $\mathrm{Nm}_{L/K}(L^\times) = \mathrm{Nm}_{E/K}(E^\times)$ (Milne, Theorem III.3.5), so that the
   intersection of the norm groups of all finite extensions is that of the abelian ones. For every finite
   extension $L/K$, the norm group
   $\mathrm{Nm}_{L/K}(L^\times)$ is open if it has finite index (Milne, Lemma I.1.3), and in characteristic
   $0$ every subgroup of finite index of $K^\times$ is open (Milne, 1.7, by Newton's lemma).

A good expansion has a page for each numbered item, with separate pages for the cup-product formula and
for the Hilbert symbol. Items 1, 2 and 3 give the existence of the local Artin map and item 4 its
uniqueness (Milne, Theorem I.1.13). Two further properties of the local Artin map that the global theory
uses are in [functoriality and explicit reciprocity](local-class-field-theory-functoriality.md).

## Depends on

- [Herbrand quotient](../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient.md), for the statements of item 2

## Proof depends on

- [Herbrand quotients agree across a map with finite kernel and cokernel](../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-finite-kernel-cokernel.md), for item 2
- [Periodicity of Tate cohomology for finite cyclic groups](../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md), for items 1 and 3
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for Tate's theorem, cup products and the inflation–restriction sequences in items 2 to 4
- [Hilbert's Theorem 90 for the multiplicative group](../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md), for $H^1(G, L^\times) = 0$ in item 2 and for the Hilbert symbol in item 4
- [The p-adic exponential on a neighbourhood of zero](p-adic-exponential.md), for an open subgroup of $U_L$ with trivial cohomology (Milne, Lemma III.2.4), in item 2

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Chapter I, Section 1 (Corollary 1.2, Lemma 1.3,
  Theorem 1.4, Corollary 1.5, 1.6, 1.7, Theorem 1.13); Chapter II, Remark 3.5 and Theorem 3.11 (Tate's
  theorem); Chapter III, Sections 1–5 (Propositions 1.1, 1.2 and 1.9, Theorem 2.1, Lemmas 2.4 and 2.5,
  Theorem 3.1, 3.3 with its footnote 3, Theorems 3.4 and 3.5, Proposition 3.6, Lemma 3.7, Propositions
  4.1 and 4.3, Theorem 4.4, Theorem 5.1); Section VIII.4 (the invariant map of $\mathbb{R}$).
