# Cohomology of the idèle group of a Galois extension

Let $L/K$ be a finite Galois extension of number fields with Galois group $G$, and let $\mathbb{I}_L$ be
the idèle group of $L$. The group $G$ acts on the places of $L$, by $|x|_{\sigma w} = |\sigma^{-1} x|_w$,
and on $\mathbb{I}_L$: for $\sigma \in G$ and $a = (a_w)_w \in \mathbb{I}_L$, the component of
$\sigma a$ at $\sigma w$ is $\sigma(a_w)$, where $\sigma \colon L_w \to L_{\sigma w}$ is the isomorphism
of completions extending $\sigma$. For each place $v$ of $K$ choose a place $w$ of $L$ above $v$, and
write $G_v \subseteq G$ for its decomposition group, which restriction identifies with
$\mathrm{Gal}(L_w/K_v)$, and $L_v = L_w$. Then:

1. The homomorphism $\mathbb{I}_K \to \mathbb{I}_L$ that puts the component $a_v$ of $a \in \mathbb{I}_K$
   at every place $w$ above $v$ is injective, with image the invariants $\mathbb{I}_L^G$.
2. For every $r \in \mathbb{Z}$ the Tate cohomology of $\mathbb{I}_L$ is the direct sum of the local
   Tate cohomology groups,

    $$\hat H^r(G, \mathbb{I}_L) \cong \bigoplus_{v} \hat H^r(G_v, L_v^\times),$$

    the sum running over all places $v$ of $K$ (for $r \ge 1$ these are the ordinary cohomology groups).
    The local groups do not depend, up to canonical isomorphism, on the choice of $w$ above $v$.

For $r = 0$, with the idèle norm $\mathrm{Nm}_{L/K} \colon \mathbb{I}_L \to \mathbb{I}_K$,
$\mathrm{Nm}_{L/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{L_w/K_v}(b_w)$, which is the map
$x \mapsto \prod_{\sigma \in G} \sigma x$ followed by the identification of part 1, part 2 says that
$a \mapsto (a_v)_v$ induces an isomorphism
$\mathbb{I}_K / \mathrm{Nm}_{L/K}(\mathbb{I}_L) \cong \bigoplus_v K_v^\times / \mathrm{Nm}_{L_w/K_v}(L_w^\times)$.

Milne's proof identifies, for each $v$, the $G$-module $\prod_{w \mid v} L_w^\times$ with the module
induced from the $G_v$-module $L_v^\times$, so that its cohomology is that of $L_v^\times$ by Shapiro's
lemma. The idèle group is the directed union of the subgroups
$\mathbb{I}_{L,S} = \prod_{w \mid v \in S} L_w^\times \times \prod_{w \mid v \notin S} \mathcal{O}_w^\times$,
for $S$ running through the finite sets of places of $K$ containing the infinite places and the places
that ramify in $L$; cohomology commutes with this union and with the products, and the factors
$\prod_{w \mid v} \mathcal{O}_w^\times$ for $v \notin S$ have zero cohomology, since the units of an
unramified extension of local fields are cohomologically trivial.

## Depends on

- [Topological idele group](../adeles-and-ideles/topological-idele-group.md)

## Proof depends on

- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the vanishing of the Tate cohomology of the units of an unramified extension (its item 1)
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for Shapiro's lemma for Tate cohomology (its item 1) and for the commutation of cohomology with products and directed unions (its item 5)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Section VII.2: Lemma 2.1 and the action of $G$ on
  $\mathbb{I}_L$, Propositions 2.2 and 2.3, Remark 2.4, Proposition 2.5 (the statement: (a) and, for
  $r \ge 0$ and with Tate groups for all $r$, (b)) with its proof, and the paragraph "The norm map on
  idèles".
