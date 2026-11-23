# The local invariants of a global class in H² sum to zero

Let $L/K$ be a finite Galois extension of number fields with Galois group $G$. For each place $v$ of $K$
choose a place $w \mid v$ of $L$, with decomposition group $G_v \cong \mathrm{Gal}(L_w/K_v)$, and let
$\mathrm{inv}_v \colon H^2(G_v, L_w^\times) \to \mathbb{Q}/\mathbb{Z}$ be the local invariant map of
$L_w/K_v$. For $\alpha \in H^2(G, L^\times)$ let $\alpha_v \in H^2(G_v, L_w^\times)$ be its image under
restriction to $G_v$ and $L^\times \subseteq L_w^\times$. Then $\alpha_v = 0$ for all but finitely many $v$,
and

$$\sum_v \mathrm{inv}_v(\alpha_v) = 0 \quad \text{in } \mathbb{Q}/\mathbb{Z}.$$

Milne's proof. The vanishing of almost all $\alpha_v$ is the
[cohomology of the idèle group](../cohomology-of-idele-classes/cohomology-of-the-idele-group.md) in degree
$2$. For a cyclic extension $L/K$ whose global Artin map is trivial on $K^\times$, the formula holds
(Lemma VII.8.5): for an injective character $\chi \colon G \to \mathbb{Q}/\mathbb{Z}$, cup product with the
class $\delta\chi \in H^2(G, \mathbb{Z})$ maps $K^\times = H^0(G, L^\times)$ onto $H^2(G, L^\times)$ by the
periodicity of the cohomology of cyclic groups, and by the local cup-product formula
$\chi(\phi_v(a)) = \mathrm{inv}_v((a \cup \delta\chi)_v)$ at every place $v$ the sum of the invariants of
$a \cup \delta\chi$ is $\chi(\phi_{L/K}(a)) = 0$. The formula is used at all places: at a real place
that becomes complex in $L$ it is the formula for $\mathbb{C}/\mathbb{R}$, and at a complex place, or a
real place that stays real, both sides vanish. By
[the cyclotomic case](principal-ideles-cyclotomic-case.md), this applies to every cyclic cyclotomic
extension. Every class of $H^2(\mathrm{Gal}(\overline{K}/K), \overline{K}^\times)$ is inflated from a
cyclic cyclotomic extension ([cyclic cyclotomic splitting](cyclic-cyclotomic-splitting.md)), and inflation
preserves the local invariants and is injective on $H^2(G, L^\times)$, which gives the formula for every
finite Galois extension (Lemma VII.8.6).

## Depends on

- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2); the proof also uses their behaviour under inflation and the cup-product formula at every place, the real ones included (its item 3)

## Proof depends on

- [Cohomology of the idèle group of a Galois extension](../cohomology-of-idele-classes/cohomology-of-the-idele-group.md), in degree $2$
- [The global Artin map of a cyclotomic extension is trivial on principal idèles](principal-ideles-cyclotomic-case.md)
- [Classes in H² of a number field split over cyclic cyclotomic extensions](cyclic-cyclotomic-splitting.md), for the splitting of every class (its part 2)
- [Global Artin map](global-artin-map.md), as the product of the local Artin maps
- [Periodicity of Tate cohomology for finite cyclic groups](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md)
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for cup products and the injectivity of inflation in degree $2$
- [Hilbert's Theorem 90 for the multiplicative group](../../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md), for the vanishing of $H^1$ of the multiplicative groups, which makes that inflation injective

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem VII.8.1(b) (the statement), Lemmas VII.8.5 and
  VII.8.6 with their proofs, and the two paragraphs between them; Proposition III.3.6 (the local
  cup-product formula); Proposition VII.2.5 (the direct sum).
