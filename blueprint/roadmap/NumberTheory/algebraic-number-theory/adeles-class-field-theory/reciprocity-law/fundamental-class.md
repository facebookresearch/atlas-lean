# Fundamental class of global class field theory

This node is still to be broken down. It covers the global analogue of the local fundamental class and the
reciprocity isomorphism it gives for every finite Galois extension, following Milne's Section VIII.4. Let
$L/K$ be a finite Galois extension of number fields of degree $n$ with Galois group $G$, and
$C_L = \mathbb{I}_L / L^\times$ its idèle class group. The statements are:

1. **The fundamental exact sequence.** Write $\mathrm{Br}(L/K) = H^2(G, L^\times)$ and
   $\mathrm{Br}(K) = H^2(\mathrm{Gal}(\overline{K}/K), \overline{K}^\times)$, and similarly for the
   completions. If the degree $n$ of $L/K$ is the least common multiple of its local degrees, in
   particular if $L/K$ is cyclic (Milne, Lemma VIII.4.1), then the sequence

    $$0 \to \mathrm{Br}(L/K) \to \bigoplus_v \mathrm{Br}(L_w/K_v) \xrightarrow{\ \sum_v \mathrm{inv}_v\ } \tfrac1n\mathbb{Z}/\mathbb{Z} \to 0$$

    is exact, $w$ being any place of $L$ above $v$ (Milne, the discussion before Lemma VIII.4.1, (a)–(c)).
    The absolute sequence

    $$0 \to \mathrm{Br}(K) \to \bigoplus_v \mathrm{Br}(K_v) \xrightarrow{\ \sum_v \mathrm{inv}_v\ } \mathbb{Q}/\mathbb{Z} \to 0$$

    is exact (Milne, Theorem VIII.4.2). Its first map is injective by the Hasse principle, the composite
    is zero because the local invariants of a global class sum to zero, and the last map is onto because
    $\mathrm{inv}_v$ is onto $\mathbb{Q}/\mathbb{Z}$ at a finite place. A family $(\beta_v)$ with
    $\sum_v \mathrm{inv}_v(\beta_v) = 0$ has finitely many nonzero components; a totally complex cyclic
    cyclotomic extension $L/K$ whose local degrees kill them (Milne, Lemma VII.7.3, with $L$ chosen totally
    complex) puts every $\beta_v$ in $\mathrm{Br}(L_w/K_v)$, and the exact sequence for the cyclic
    extension $L/K$ gives a global class with these components. Milne's own proof of Theorem VIII.4.2
    passes to the limit over the fields $\Omega_n$ below; since $\mathbb{Q}^c$ is totally real, that limit
    reaches only the groups $\mathrm{Br}(\Omega_v/K_v)$, which are $0$ at the real places of $K$ that stay
    real in $\Omega$, instead of $\mathrm{Br}(K_v) = \tfrac12\mathbb{Z}/\mathbb{Z}$; the argument above
    avoids this. For every finite Galois extension $L/K$, the snake lemma then gives the exact sequence
    above, ending in $\tfrac{1}{n_0}\mathbb{Z}/\mathbb{Z}$, $n_0$ the least common multiple of the local
    degrees (Milne, Corollary VIII.4.3, stated there for every finite extension).

2. **The fundamental class.** Let $\mathbb{Q}^c$ be the infinite cyclic cyclotomic extension of
   $\mathbb{Q}$, with Galois group $\hat{\mathbb{Z}}$, which is totally real (Milne, Example I.A.5(d)), let
   $\Omega = \mathbb{Q}^c K$ and let $\Omega_n \subseteq \Omega$ be the cyclic extension of $K$ of degree
   $n$. For each place $v$ of $K$ let $\mathrm{Br}(\Omega_v/K_v)$ be the union of the relative groups
   $\mathrm{Br}(\Omega_{n,w}/K_v)$. It is $\mathrm{Br}(K_v)$ for $v$ finite: for every prime $\ell$ the
   local degrees at $v$ of the $\ell$-power layers of $\Omega/K$ are unbounded, since those of
   $\mathbb{Q}^c$ at every prime are (Milne, proof of Lemma VII.7.3), so every integer $d$ divides the local
   degree $[\Omega_{n,w} : K_v]$ for a suitable $n$, and $\Omega_n$ then splits every class of order $d$ in
   $\mathrm{Br}(K_v) \cong \mathbb{Q}/\mathbb{Z}$. It is $0$ at a real place of $K$ that is real in $\Omega$.
   The exact sequences of item 1 for the cyclic extensions $\Omega_n/K$ give an isomorphism
   $\mathrm{inv}_K \colon H^2(\mathrm{Gal}(\Omega/K), C_\Omega) \to \mathbb{Q}/\mathbb{Z}$, the only one whose
   composite with the map from $\bigoplus_v \mathrm{Br}(\Omega_v/K_v)$ is $\sum_v \mathrm{inv}_v$, where
   $H^2(\mathrm{Gal}(\Omega/K), C_\Omega)$ is the union of the groups $H^2(\mathrm{Gal}(\Omega_n/K), C_{\Omega_n})$.
   Since the global invariants multiply by the degree under restriction (Milne, Lemma VIII.4.6), they give
   isomorphisms $\mathrm{inv}_{L/K} \colon H^2(G, C_L) \to \tfrac1n\mathbb{Z}/\mathbb{Z}$, so $H^2(G, C_L)$ is
   cyclic of order $n$ with the canonical generator $u_{L/K}$ of invariant $1/n$, the fundamental class
   (Milne, Theorem VIII.4.7); for a tower $E \supseteq L \supseteq K$ of finite Galois extensions,
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
- [The local invariants of a global class in H² sum to zero](sum-of-local-invariants.md), for the composite in item 1
- [Classes in H² of a number field split over cyclic cyclotomic extensions](cyclic-cyclotomic-splitting.md), for the totally complex cyclic cyclotomic extensions of its part 1, in item 1
- [Frobenius elements generate the Galois group of a solvable extension](../cohomology-of-idele-classes/frobenius-elements-generate.md), for Lemma VIII.4.1 (its part 3)
- [Second inequality of global class field theory](../cohomology-of-idele-classes/second-inequality.md), for $H^1(G, C_L) = 0$ and the order of $H^2(G, C_L)$, in items 1 to 3
- [Cohomology of the idèle group of a Galois extension](../cohomology-of-idele-classes/cohomology-of-the-idele-group.md), for $H^2(G, \mathbb{I}_L) \cong \bigoplus_v \mathrm{Br}(L_w/K_v)$ in item 1
- [Hilbert's Theorem 90 for the multiplicative group](../../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md), for $H^1(G, L^\times) = 0$, which makes the relative Brauer groups subgroups of $\mathrm{Br}(K)$, in item 1
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2)
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for the inflation–restriction sequences in item 1, Tate's theorem and its compatibility with corestriction (its items 1, 2 and 4)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Section VIII.4, "The Fundamental Exact Sequence and the
  Fundamental Class" (the discussion before Lemma 4.1, Lemma 4.1, Theorem 4.2, Corollary 4.3, Lemma 4.6,
  Theorem 4.7 and the paragraph after it); Example I.A.5(d) (the field $\mathbb{Q}^c$); Proposition
  II.1.22 ($H^1(G, L^\times) = 0$); Theorem II.3.11 (Tate's theorem); Proposition VII.7.2, Lemma VII.7.3
  and Theorem VII.8.1(b).
