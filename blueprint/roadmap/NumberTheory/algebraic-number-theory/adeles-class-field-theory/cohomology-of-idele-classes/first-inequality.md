# First inequality of global class field theory

Let $L/K$ be a cyclic extension of number fields of degree $n$ with Galois group $G$, and let
$C_L = \mathbb{I}_L / L^\times$ be the idèle class group of $L$, with the action of $G$ induced by its
action on the idèles. Then the Herbrand quotient
$h(C_L) = |\hat H^0(G, C_L)| / |\hat H^{-1}(G, C_L)|$ is defined and

$$h(C_L) = n.$$

Consequently, with the idèle norm $\mathrm{Nm}_{L/K} \colon \mathbb{I}_L \to \mathbb{I}_K$,
$\mathrm{Nm}_{L/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{L_w/K_v}(b_w)$, the index
$(\mathbb{I}_K : K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L))$ is finite and at least $n$ (the first
inequality): it is $|\hat H^0(G, C_L)| = n \, |\hat H^{-1}(G, C_L)|$, by the
[Galois invariants of the idèle class group](galois-invariants-of-idele-classes.md) and the
[Herbrand quotient as a ratio of orders](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-eq.md).

Milne's proof chooses a finite set $S$ of places of $K$ containing the infinite places, the places that
ramify in $L$ and the places below a set of prime ideals of $L$ generating the class group of $L$, which
is finite by [Minkowski's bound](../../number-fields-embeddings/minkowski-bound.md). With $T$ the set of
places of $L$ above $S$, every idèle of $L$ is then a principal idèle times a $T$-idèle, so $C_L \cong \mathbb{I}_{L,T} / U(T)$, where
$\mathbb{I}_{L,T} = \prod_{w \in T} L_w^\times \times \prod_{w \notin T} \mathcal{O}_w^\times$ and
$U(T) = L^\times \cap \mathbb{I}_{L,T}$ is the group of $T$-units. By multiplicativity,
$h(C_L) = h(\mathbb{I}_{L,T}) / h(U(T))$, and the
[Herbrand quotient of the T-idèles](herbrand-quotient-of-t-ideles.md) and the
[Herbrand quotient of the T-units](herbrand-quotient-of-t-units.md) give
$\prod_{v \in S} n_v \big/ \bigl(n^{-1} \prod_{v \in S} n_v\bigr) = n$. Milne's Herbrand quotient has
$|H^1(G, C_L)|$ in the denominator; for cyclic $G$ this group is isomorphic to $\hat H^{-1}(G, C_L)$ by the
[periodicity of Tate cohomology](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md),
so the two statements agree.

## Depends on

- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)
- [Herbrand quotient](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient.md)

## Proof depends on

- [Herbrand quotient of the T-idèles of a cyclic extension](herbrand-quotient-of-t-ideles.md)
- [Herbrand quotient of the T-units of a cyclic extension](herbrand-quotient-of-t-units.md)
- [Multiplicativity of the Herbrand quotient in short exact sequences](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-mul-of-short-exact.md)
- [Galois invariants of the idèle class group](galois-invariants-of-idele-classes.md), for $\hat H^0(G, C_L) \cong \mathbb{I}_K / K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L)$ in the consequence
- [Herbrand quotient as a ratio of orders](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-eq.md), for $h(C_L) = |\hat H^0(G, C_L)| / |\hat H^{-1}(G, C_L)|$ once both groups are finite
- [Minkowski's bound: every ideal class of a number field contains an integral ideal of small norm](../../number-fields-embeddings/minkowski-bound.md), for the finiteness of the class group of $L$: each class contains an integral ideal of norm at most the bound, and there are finitely many such ideals
- [Periodicity of Tate cohomology for finite cyclic groups](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md), for comparing with Milne's Herbrand quotient

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem VII.4.3 ($h(C_L) = [L : K]$) and its proof,
  Lemma VII.4.2 ($\mathbb{I}_L = L^\times \mathbb{I}_{L,T}$ when $T$ contains generators of the class
  group), Corollary VII.4.4 (the first inequality).
