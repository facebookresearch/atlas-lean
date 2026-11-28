/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Coxeter.Matrix

/-!
# Artin groups (Artin–Tits groups) of a Coxeter matrix

Given a Coxeter matrix `M` over an index type `B` (a symmetric matrix `M : Matrix B B ℕ` with
`M i i = 1` and `M i i' ≠ 1` for `i ≠ i'`, using the Mathlib convention `M i i' = 0 ↔ m i i' = ∞`),
its **Artin group** (or **Artin–Tits group**) is the group presented by generators `s i`, one for
each `i : B`, subject only to the braid relations

`s i * s j * s i * ⋯ = s j * s i * s j * ⋯`   (both words of length `M i j`),

one for each pair of distinct generators with a finite entry `M i j ≠ ∞`. The relation is omitted
when `M i j = ∞` (encoded as `M i j = 0`).

Adding the involution relations `s i ^ 2 = 1` to this presentation yields the Coxeter group
`M.Group`; equivalently, the quotient of the Artin group killing `s i ^ 2` recovers the Coxeter
group. (Merely deleting the involutions from the Coxeter presentation would leave power
relators `(s i * s j) ^ (M i j) = 1` instead of the braid equalities, a different group.) In
particular the braid group on `n + 1` strands is the Artin group of the type `Aₙ` Coxeter matrix.

## Main definitions

* `CoxeterMatrix.alternatingWord a b n`: the alternating product `a * b * a * ⋯` of length `n` in a
  monoid, starting with `a`.
* `CoxeterMatrix.artinRelation M i j`: the braid relation for the pair `(i, j)`, encoded as an
  element of the free group.
* `CoxeterMatrix.artinRelationsSet M`: the set of all braid relations of `M`.
* `CoxeterMatrix.ArtinGroup M`: the Artin group of `M`, presented on `B` by `artinRelationsSet M`.
* `CoxeterMatrix.ArtinGroup.of M i`: the generator `s i`.

## Main results

* `CoxeterMatrix.ArtinGroup.closure_range_of`: the generators generate the whole Artin group.
* `CoxeterMatrix.ArtinGroup.braid_relation`: the defining braid relation holds among the generators.

## References

* E. Brieskorn and K. Saito, *Artin-Gruppen und Coxeter-Gruppen*, Invent. Math. 17 (1972), 245-271.
* J. Tits, *Normalisateurs de tores I*, J. Algebra 4 (1966), 96-116.

## Tags

Artin group, Artin-Tits group, braid group, Coxeter matrix, presented group
-/

@[expose] public section

namespace CoxeterMatrix

variable {B : Type*}

/-- **Alternating word.** For elements $a$ and $b$ of a monoid and $n \in \mathbb{N}$, the
alternating word of length $n$ starting with $a$ is the product $a b a b \cdots$ of $n$ factors
that alternate between $a$ and $b$, beginning with $a$; for $n = 0$ it is the identity. -/
def alternatingWord {G : Type*} [Monoid G] (a b : G) : ℕ → G
  | 0 => 1
  | n + 1 => a * alternatingWord b a n

@[simp]
theorem alternatingWord_zero {G : Type*} [Monoid G] (a b : G) : alternatingWord a b 0 = 1 := rfl

@[simp]
theorem alternatingWord_succ {G : Type*} [Monoid G] (a b : G) (n : ℕ) :
    alternatingWord a b (n + 1) = a * alternatingWord b a n := rfl

/-- **Monoid homomorphisms preserve alternating words.** Let $f : G \to H$ be a homomorphism of
monoids. For all $a, b \in G$ and $n \in \mathbb{N}$, $f$ maps the alternating word $a b a \cdots$
of length $n$ starting with $a$ to the alternating word $f(a) f(b) f(a) \cdots$ of length $n$
starting with $f(a)$. -/
theorem map_alternatingWord {G H : Type*} [Monoid G] [Monoid H] (f : G →* H) (a b : G) (n : ℕ) :
    f (alternatingWord a b n) = alternatingWord (f a) (f b) n := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih => simp [alternatingWord, ih]

variable (M : CoxeterMatrix B)

/-- **Artin relator.** Let $M = (m_{ij})$ be a Coxeter matrix over an index type $B$, and write
$s_i$ for the free generators of the free group on $B$. For $i, j \in B$, let $u$ and $v$ be the
alternating words $s_i s_j s_i \cdots$ and $s_j s_i s_j \cdots$ of length $m_{ij}$. The Artin
relator of the ordered pair $(i, j)$ is the element $u v^{-1}$ of the free group; setting it equal
to $1$ imposes the braid relation $u = v$. -/
def artinRelation (i j : B) : FreeGroup B :=
  alternatingWord (FreeGroup.of i) (FreeGroup.of j) (M i j) *
    (alternatingWord (FreeGroup.of j) (FreeGroup.of i) (M i j))⁻¹

/-- **Artin relators of a Coxeter matrix.** Let $M = (m_{ij})$ be a Coxeter matrix over an index
type $B$, where $m_{ij} = 0$ encodes $m_{ij} = \infty$, and write $s_i$ for the free generators of
the free group on $B$. The set of Artin relators of $M$ consists of the elements $u v^{-1}$ of the
free group, one for each ordered pair of distinct $i, j \in B$ with $m_{ij} \neq 0$, where $u$ and
$v$ are the alternating words $s_i s_j s_i \cdots$ and $s_j s_i s_j \cdots$ of length $m_{ij}$.
Pairs with $m_{ij} = \infty$ contribute no relator. -/
def artinRelationsSet : Set (FreeGroup B) :=
  { r | ∃ i j, i ≠ j ∧ M i j ≠ 0 ∧ r = M.artinRelation i j }

/-- **Artin group.** Let $M = (m_{ij})_{i, j \in B}$ be a Coxeter matrix over an index type $B$,
where $m_{ij} = 0$ encodes $m_{ij} = \infty$. The Artin group (Artin–Tits group) of $M$ is the
group presented by generators $s_i$, one for each $i \in B$, subject only to the braid relations:
for every ordered pair of distinct $i, j \in B$ with $m_{ij} \neq 0$, the alternating words
$s_i s_j s_i \cdots$ and $s_j s_i s_j \cdots$ of length $m_{ij}$ are equal. Unlike for the
Coxeter group of $M$, no relations $s_i^2 = 1$ are imposed. -/
def ArtinGroup := PresentedGroup M.artinRelationsSet

instance : Group M.ArtinGroup := inferInstanceAs (Group (PresentedGroup _))

namespace ArtinGroup

/-- **Generators of the Artin group.** For a Coxeter matrix $M$ over an index type $B$ and
$i \in B$, the generator $s_i$ of the Artin group of $M$ is the image of the free generator $i$
under the quotient map from the free group on $B$ onto the Artin group. -/
def of (i : B) : M.ArtinGroup := PresentedGroup.of i

/-- **The generators generate the Artin group.** For a Coxeter matrix $M$ over an index type $B$,
the subgroup of the Artin group of $M$ generated by its generators $s_i$, $i \in B$, is the whole
group. -/
theorem closure_range_of : Subgroup.closure (Set.range (of M)) = ⊤ :=
  PresentedGroup.closure_range_of _

/-- **Braid relations in the Artin group.** Let $M = (m_{ij})$ be a Coxeter matrix over an index
type $B$, where $m_{ij} = 0$ encodes $m_{ij} = \infty$, and let $s_i$ ($i \in B$) be the
generators of the Artin group of $M$. For distinct $i, j \in B$ with $m_{ij} \neq 0$, the
alternating words $s_i s_j s_i \cdots$ and $s_j s_i s_j \cdots$ of length $m_{ij}$ are equal in
the Artin group. -/
theorem braid_relation {i j : B} (hij : i ≠ j) (h : M i j ≠ 0) :
    alternatingWord (of M i) (of M j) (M i j) = alternatingWord (of M j) (of M i) (M i j) := by
  have hmem : M.artinRelation i j ∈ M.artinRelationsSet := ⟨i, j, hij, h, rfl⟩
  have key := PresentedGroup.mk_eq_mk_of_mul_inv_mem hmem
  rwa [map_alternatingWord (PresentedGroup.mk _), map_alternatingWord (PresentedGroup.mk _)] at key

end ArtinGroup

end CoxeterMatrix
