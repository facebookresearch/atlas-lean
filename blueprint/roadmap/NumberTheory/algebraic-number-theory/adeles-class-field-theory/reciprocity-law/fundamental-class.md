# Fundamental class of global class field theory

This node is still to be broken down. It covers the global analogue of the local fundamental class and the
reciprocity isomorphism it gives for every finite Galois extension, following Milne's Section VIII.4. Let
$L/K$ be a finite Galois extension of number fields of degree $n$ with Galois group $G$, and
$C_L = \mathbb{I}_L / L^\times$ its idèle class group. The statements are:

1. **The fundamental exact sequence.** The sequence
   $$0 \to H^2(\mathrm{Gal}(\overline{K}/K), \overline{K}^\times) \to \bigoplus_v H^2(\mathrm{Gal}(\overline{K}_v/K_v), \overline{K}_v^\times) \xrightarrow{\ \sum_v \mathrm{inv}_v\ } \mathbb{Q}/\mathbb{Z} \to 0$$
   is exact, that is, $0 \to \mathrm{Br}(K) \to \bigoplus_v \mathrm{Br}(K_v) \to \mathbb{Q}/\mathbb{Z} \to 0$
   (Milne, Theorem VIII.4.2), and for $L/K$ the corresponding sequence ends in
   $\tfrac{1}{n_0}\mathbb{Z}/\mathbb{Z}$, $n_0$ the least common multiple of the local degrees (Corollary
   VIII.4.3). For cyclic $L/K$, $n_0 = n$ (Lemma VIII.4.1).
2. **The fundamental class.** Let $\Omega = \mathbb{Q}^c K$, where $\mathbb{Q}^c$ is the infinite cyclic
   cyclotomic extension of $\mathbb{Q}$ (Milne, I A.5(d) and Lemma VII.7.3). There is a unique isomorphism
   $\mathrm{inv}_K \colon H^2(\mathrm{Gal}(\Omega/K), C_\Omega) \to \mathbb{Q}/\mathbb{Z}$ whose composite
   with the map from $\bigoplus_v \mathrm{Br}(K_v)$ is $\sum_v \mathrm{inv}_v$; since the global invariants
   multiply by the degree under restriction (Lemma VIII.4.6), they give isomorphisms
   $\mathrm{inv}_{L/K} \colon H^2(G, C_L) \to \tfrac1n\mathbb{Z}/\mathbb{Z}$, so $H^2(G, C_L)$ is cyclic of
   order $n$ with the canonical generator $u_{L/K}$ of invariant $1/n$, the fundamental class (Theorem
   VIII.4.7); for a tower $E \supseteq L \supseteq K$ of finite Galois extensions,
   $\mathrm{Res}(u_{E/K}) = u_{E/L}$ and $\mathrm{Inf}(u_{L/K}) = [E : L] \, u_{E/K}$.
3. **Reciprocity for Galois extensions.** By Tate's theorem, cup product with $u_{L/K}$ is an isomorphism
   $\hat H^r(G, \mathbb{Z}) \to \hat H^{r+2}(G, C_L)$ for all $r$; for $r = -2$ it is an isomorphism
   $G^{\mathrm{ab}} \to C_K / \mathrm{Nm}_{L/K}(C_L)$. For an intermediate field $E$, these isomorphisms for
   $L/E$ and $L/K$ are compatible with corestriction: the map
   $\mathrm{Gal}(L/E)^{\mathrm{ab}} \to G^{\mathrm{ab}}$ induced by the inclusion corresponds to the norm
   $C_E / \mathrm{Nm}_{L/E}(C_L) \to C_K / \mathrm{Nm}_{L/K}(C_L)$. Milne states, without proof, that for
   abelian $L/K$ the inverse of this isomorphism is the global Artin map of $L/K$, because the global and
   local fundamental classes are compatible.

A good expansion has pages for the fundamental exact sequence, with Lemma VIII.4.1 and Corollary
VIII.4.3; for the global invariant map and the fundamental class with its restriction and inflation
formulas; and for the reciprocity isomorphism of item 3 with its compatibility with corestriction and with
the global Artin map.

## Depends on

- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [Hasse principle for H² of the multiplicative group of a number field](hasse-principle-for-h2.md), for the injectivity in item 1
- [Classes in H² of a number field split over cyclic cyclotomic extensions](cyclic-cyclotomic-splitting.md), for item 1, with Lemma VII.7.3 from its proof
- [The local invariants of a global class in H² sum to zero](sum-of-local-invariants.md), for item 1
- [Frobenius elements generate the Galois group of a solvable extension](../cohomology-of-idele-classes/frobenius-elements-generate.md), for Lemma VIII.4.1
- [Second inequality of global class field theory](../cohomology-of-idele-classes/second-inequality.md), for $H^1(G, C_L) = 0$ and the order of $H^2(G, C_L)$, in items 1 to 3
- [Cohomology of the idèle group of a Galois extension](../cohomology-of-idele-classes/cohomology-of-the-idele-group.md), in degree $2$
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2)
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for Tate's theorem and its compatibility with corestriction (its items 1 and 4)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Section VIII.4, "The Fundamental Exact Sequence and the
  Fundamental Class" (Lemma 4.1, Theorem 4.2, Corollary 4.3, Lemma 4.6, Theorem 4.7 and the paragraph after
  it); Theorem II.3.11 (Tate's theorem); Proposition VII.7.2 and Lemma VII.7.3.
