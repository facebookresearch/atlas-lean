# S-units that are local n-th powers are global n-th powers

Let $n \ge 1$ and let $K$ be a number field containing a primitive $n$-th root of unity. Let $S$ be a finite
set of places of $K$ containing the infinite places and the places dividing $n$, large enough that
$\mathbb{I}_K = K^\times \mathbb{I}_{K,S}$, where
$\mathbb{I}_{K,S} = \prod_{v \in S} K_v^\times \times \prod_{v \notin S} \mathcal{O}_v^\times$ (as happens when $S$
contains a set of prime ideals generating the class group). Let $T$ be a finite set of finite places of
$K$, disjoint from $S$, such that the map

$$U(S) \to \prod_{v \in T} \mathcal{O}_v^\times / \mathcal{O}_v^{\times n}$$

from the group $U(S)$ of $S$-units is surjective. If $b \in K^\times$ is an $n$-th power in $K_v$ for every
$v \in S$ and a unit at every place outside $S \cup T$, then $b$ is an $n$-th power in $K$.

For $T = \emptyset$ the hypothesis on $T$ is empty, and the statement says that an $S$-unit that is an
$n$-th power in $K_v$ for every $v \in S$ is an $n$-th power in $K$.

Milne's proof: let $L = K[b^{1/n}]$, an abelian extension of $K$ whose Galois group is killed by $n$
([Kummer theory](../../../../FieldTheory/galois-theory/kummer-theory.md)), and let
$D = \prod_{v \in S} K_v^\times \times \prod_{v \in T} \mathcal{O}_v^{\times n} \times \prod_{v \notin S \cup T} \mathcal{O}_v^\times$.
Then $D \subseteq \mathrm{Nm}_{L/K}(\mathbb{I}_L)$: for $v \in S$, $X^n - b$ splits in $K_v$, so $L_w = K_v$;
for $v \in T$, the index of the local norm group is $[L_w : K_v]$, which divides $n$, by the
[local Artin map](../../../p-adic-numbers/local-class-field-theory.md); for $v \notin S \cup T$, $L_w/K_v$ is
unramified, since $n$ and $b$ are both units at $v$ and so $v$ does not divide the discriminant
$\pm n^n b^{n-1}$ of $X^n - b$, and the norm maps units onto units. The surjectivity hypothesis gives
$\mathbb{I}_{K,S} = D \, U(S)$, so $K^\times D = \mathbb{I}_K$, and the
[density criterion](norm-density-criterion.md) gives $L = K$.

## Depends on

- [Places of a number field](../places-of-a-number-field/place.md)
- [Topological idele group](../adeles-and-ideles/topological-idele-group.md)

## Proof depends on

- [Kummer theory for abelian extensions of exponent dividing n](../../../../FieldTheory/galois-theory/kummer-theory.md), for the extension $K[b^{1/n}]/K$
- [Local class field theory: the local Artin map](../../../p-adic-numbers/local-class-field-theory.md), for the index of the local norm groups at the places of $T$
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the norm of units in unramified extensions (its item 1)
- [A solvable extension with norms dense modulo principal idèles is trivial](norm-density-criterion.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Proposition VII.6.10 (the statement) and its proof;
  Proposition VII.9.2 (the case $T = \emptyset$, with $S$ containing generators of the class group) and
  its footnote 7 (the proof uses only Lemma VII.4.5); Proposition VII.A.5 (the discriminant of
  $X^n - a$).
