# Hasse principle for H² of the multiplicative group of a number field

Let $L/K$ be a finite Galois extension of number fields with Galois group $G$. For each place $v$ of $K$
choose a place $w$ of $L$ above $v$, with decomposition group $G_v \cong \mathrm{Gal}(L_w/K_v)$. Then the
homomorphism

$$H^2(G, L^\times) \to \bigoplus_v H^2(G_v, L_w^\times),$$

whose component at $v$ is restriction to $G_v$ followed by the map induced by $L^\times \subseteq L_w^\times$,
is well defined (a class has nonzero image at only finitely many $v$) and injective. Passing to the direct
limit over the finite Galois subextensions, the same holds for every infinite Galois extension, in
particular for an algebraic closure $\overline{K}$ of $K$: a class in
$H^2(\mathrm{Gal}(\overline{K}/K), \overline{K}^\times)$ (continuous cohomology) whose restriction to the
decomposition group of every place vanishes in $H^2(\mathrm{Gal}(\overline{K}_v/K_v), \overline{K}_v^\times)$ is
zero.

Milne's Chapter IV identifies $H^2(\mathrm{Gal}(L/K), L^\times)$ with the relative Brauer group
$\mathrm{Br}(L/K)$; in those terms, a central simple algebra over $K$ that splits over every completion
$K_v$ splits over $K$.

Milne's proof: since $H^1(G, C_L) = 0$ by the [second inequality](../cohomology-of-idele-classes/second-inequality.md),
the cohomology sequence of $1 \to L^\times \to \mathbb{I}_L \to C_L \to 1$ makes
$H^2(G, L^\times) \to H^2(G, \mathbb{I}_L)$ injective, and the
[cohomology of the idèle group](../cohomology-of-idele-classes/cohomology-of-the-idele-group.md)
identifies $H^2(G, \mathbb{I}_L)$ with $\bigoplus_v H^2(G_v, L_w^\times)$.

## Depends on

- [Places of a number field](../places-of-a-number-field/place.md)

## Proof depends on

- [Second inequality of global class field theory](../cohomology-of-idele-classes/second-inequality.md), for $H^1(G, C_L) = 0$
- [Cohomology of the idèle group of a Galois extension](../cohomology-of-idele-classes/cohomology-of-the-idele-group.md), in degree $2$
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for the injectivity of inflation in degree $2$, used in the passage to the limit
- [Hilbert's Theorem 90 for the multiplicative group](../../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md), for the vanishing of $H^1$ of the multiplicative groups, which makes that inflation injective

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem VII.7.1 (the statement, for every Galois
  extension, possibly infinite) and its proof; the remarks at the start of Section VII.7 and after Lemma
  VII.7.3 (the interpretation by Brauer groups and central simple algebras).
