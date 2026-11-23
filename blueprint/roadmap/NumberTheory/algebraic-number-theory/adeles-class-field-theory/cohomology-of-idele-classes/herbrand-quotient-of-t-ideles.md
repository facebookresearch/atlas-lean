# Herbrand quotient of the T-idèles of a cyclic extension

Let $L/K$ be a cyclic extension of number fields with Galois group $G$, let $S$ be a finite set of places
of $K$ containing the infinite places, and let $T$ be the set of places of $L$ above $S$. Let

$$\mathbb{I}_{L,T} = \prod_{w \in T} L_w^\times \times \prod_{w \notin T} \mathcal{O}_w^\times \subseteq \mathbb{I}_L$$

be the group of $T$-idèles, which is stable under the action of $G$ on the idèles ($\sigma a$ has
component $\sigma(a_w)$ at $\sigma w$). Then the Herbrand quotient
$h(\mathbb{I}_{L,T}) = |\hat H^0(G, \mathbb{I}_{L,T})| / |\hat H^{-1}(G, \mathbb{I}_{L,T})|$ is defined
and

$$h(\mathbb{I}_{L,T}) = \prod_{v \in S} n_v,$$

where $n_v = [L_w : K_v]$ is the local degree at $v$, for any place $w$ of $L$ above $v$.

Milne's proof: by Shapiro's lemma the $G$-module $\prod_{w \mid v} L_w^\times$ has the Tate cohomology of
the $G_v$-module $L_w^\times$, where $G_v \cong \mathrm{Gal}(L_w/K_v)$ is the decomposition group of $w$,
and similarly for $\prod_{w \mid v} \mathcal{O}_w^\times$. The local extensions $L_w/K_v$ are cyclic, and
local class field theory gives $h(L_w^\times) = n_v$ and $h(\mathcal{O}_w^\times) = 1$, the cohomology of
$\mathcal{O}_w^\times$ being zero when $L_w/K_v$ is unramified. Since Tate cohomology commutes with
products, the Herbrand quotient of the factor $\prod_{w \notin T} \mathcal{O}_w^\times$ is $1$ and
$h(\mathbb{I}_{L,T}) = \prod_{v \in S} h(L_w^\times)$.

## Depends on

- [Topological idele group](../adeles-and-ideles/topological-idele-group.md)
- [Herbrand quotient](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient.md)

## Proof depends on

- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the Herbrand quotients $h(L_w^\times) = n_v$ and $h(\mathcal{O}_w^\times) = 1$ of a cyclic extension of local fields (its item 2) and the vanishing of the cohomology of the units of an unramified one (its item 1)
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for Shapiro's lemma for Tate cohomology (its item 1) and the Tate cohomology of products (its item 5)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Proposition VII.2.7 (the statement, with $S$
  containing the infinite places as in Sections VII.3 and VII.4) and its proof, through Proposition
  VII.2.3 and Lemma III.2.5.
