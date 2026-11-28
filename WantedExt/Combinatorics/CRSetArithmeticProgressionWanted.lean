/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.PNat.Basic
public import MathlibExt.Combinatorics.CRSetArithmeticProgression
public import MathlibExt.Combinatorics.EssentialCRSet
public import MathlibExt.Combinatorics.EssentialSetSequence
public import MathlibExt.Combinatorics.RamseyFamily
public import MathlibExt.Combinatorics.RamseyFamilyIdempotent
public import MathlibExt.Combinatorics.RamseyFamilyDecreasingSequenceIdempotent

/-!
# Arithmetic progressions in CR-sets

Statements from Dibyendu De and Pintu Debnath, *Abundance of Arithmetic
Progressions in CR-Sets*, INTEGERS 25 (2025), Article A4 (arXiv:2211.12372).

The paper works in a commutative semigroup `(S, +)`; finite sums in `S` are written
as left folds `List.foldl (· + ·) s l`, so no additive identity is needed. The
progression `a, a + b, …, a + l b` is written `(· + b)^[i] a` for `i ≤ l`. The
paper's `ℕ` is the positive integers, modelled by `ℕ+`.

Ultrafilters are multiplied with Mathlib's `Ultrafilter.semigroup`, for which
`A ∈ p * q` iff `{x | {y | x * y ∈ A} ∈ q} ∈ p`; this is the paper's convention,
and `q ↦ q * p` is continuous (`Ultrafilter.continuous_mul_left`), so `βS` is the
paper's compact right topological semigroup.

`MetaMathlibExt.IsPiecewiseSyndetic` (WantedExt/Combinatorics/PiecewiseSyndeticWanted.lean)
is specific to `ℕ^t` with its cube geometry; Theorem 1 here needs `ℤ` and `ℤ × ℤ`,
so the general semigroup notion of the paper is defined separately.
-/

namespace MetaMathlibExt

@[expose] public section

attribute [local instance] Ultrafilter.semigroup Ultrafilter.addSemigroup

section Largeness

variable {S : Type*} [AddCommSemigroup S]

/-- **Thick set in a commutative semigroup.** A subset $A$ of a commutative semigroup $(S, +)$ is
thick when for every finite set $E \subseteq S$ there is an $x \in S$ with $E + x \subseteq A$,
that is, $e + x \in A$ for every $e \in E$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of thick sets). -/
def IsAddThick (A : Set S) : Prop :=
  ∀ E : Finset S, ∃ x : S, ∀ e ∈ E, e + x ∈ A

/-- **Piecewise syndetic set in a commutative semigroup.** A subset $A$ of a commutative semigroup
$(S, +)$ is piecewise syndetic when there is a finite set $F \subseteq S$ such that the union
$\bigcup_{t \in F} (-t + A)$ is thick, where $-t + A = \{s \in S : t + s \in A\}$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of piecewise syndetic sets). -/
def IsAddPiecewiseSyndetic (A : Set S) : Prop :=
  ∃ F : Finset S, IsAddThick (⋃ t ∈ F, {s : S | t + s ∈ A})

/-- **J-sets in commutative semigroups.** Let $S$ be a commutative semigroup and let
$\mathbb{N} = \{0, 1, 2, \dots\}$. A set $A \subseteq S$ is a $J$-set when for every finite set
$F$ of sequences $f \colon \mathbb{N} \to S$ there are $a \in S$ and a nonempty finite set
$H \subseteq \mathbb{N}$ such that $a + \sum_{n \in H} f(n) \in A$ for every $f \in F$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 1. -/
def IsJSet (A : Set S) : Prop :=
  ∀ F : Finset (ℕ → S), ∃ a : S, ∃ H : List ℕ, H.Nodup ∧ H ≠ [] ∧
    ∀ f ∈ F, (H.map f).foldl (· + ·) a ∈ A

/-- **The whole commutative semigroup is thick.** If $S$ is a nonempty commutative semigroup,
then $S$ itself is a thick subset of $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of thick sets). -/
theorem isAddThick_univ [Nonempty S] : IsAddThick (Set.univ : Set S) :=
  fun _ => ⟨Classical.arbitrary S, fun _ _ => Set.mem_univ _⟩

/-- **The empty set is not thick.** In a nonempty commutative semigroup, the empty set is not
thick.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of thick sets). -/
theorem not_isAddThick_empty [Nonempty S] : ¬ IsAddThick (∅ : Set S) := by
  intro h
  obtain ⟨x, hx⟩ := h {Classical.arbitrary S}
  exact hx _ (Finset.mem_singleton_self _)

/-- **The whole commutative semigroup is piecewise syndetic.** If $S$ is a nonempty commutative
semigroup, then $S$ itself is a piecewise syndetic subset of $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of piecewise syndetic sets). -/
theorem isAddPiecewiseSyndetic_univ [Nonempty S] :
    IsAddPiecewiseSyndetic (Set.univ : Set S) :=
  ⟨{Classical.arbitrary S}, fun _ => ⟨Classical.arbitrary S, fun _ _ => by simp⟩⟩

/-- **The whole semigroup is a J-set.** In every nonempty commutative semigroup $S$, the set $S$
itself is a $J$-set.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 1. -/
theorem isJSet_univ [Nonempty S] : IsJSet (Set.univ : Set S) :=
  fun _ => ⟨Classical.arbitrary S, [0], List.nodup_singleton 0, List.cons_ne_nil _ _,
    fun _ _ => Set.mem_univ _⟩

/-- **The whole commutative semigroup is a CR-set.** If $S$ is a nonempty commutative semigroup,
then $S$ itself is a CR-set in $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 2. -/
theorem isCRSet_univ [Nonempty S] : IsCRSet (Set.univ : Set S) :=
  fun _ => ⟨1, fun _ => ⟨Finset.univ, Finset.univ_nonempty, Classical.arbitrary S,
    fun _ => Set.mem_univ _⟩⟩

/-- **The empty set is not a CR-set.** In every commutative semigroup, the empty set is not a
CR-set.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 2. -/
theorem not_isCRSet_empty : ¬ IsCRSet (∅ : Set S) := by
  intro h
  obtain ⟨r₀, hr₀⟩ := h 0
  obtain ⟨-, -, s, -⟩ := hr₀ fun _ => Fin.elim0
  obtain ⟨r, hr⟩ := h 1
  obtain ⟨α, -, t, ht⟩ := hr fun _ _ => s
  exact ht 0

end Largeness

section Families

variable {S : Type*}

end Families

/-- **Furstenberg–Glasner theorem on progressions in piecewise syndetic sets.** If
$S \subseteq \mathbb{Z}$ is piecewise syndetic, then for every natural number $k$ the set of pairs
$(a, d) \in \mathbb{Z} \times \mathbb{Z}$ such that $a + i d \in S$ for all $i = 0, 1, \dots, k$
is piecewise syndetic in $\mathbb{Z} \times \mathbb{Z}$.

The paper takes $k \ge 1$; the case $k = 0$ is included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 1 (`integers-2025-A4-thm-1`). -/
public theorem_wanted IsAddPiecewiseSyndetic.arithmeticProgressions_int {S : Set ℤ}
    (hS : IsAddPiecewiseSyndetic S) (k : ℕ) :
    IsAddPiecewiseSyndetic {p : ℤ × ℤ | ∀ i ≤ k, p.1 + i * p.2 ∈ S}

/-- **Debnath–Goswami theorem on progressions in J-sets.** Let $\mathbb{N}^+$ denote the
positive integers under addition. If $S \subseteq \mathbb{N}^+$ is a $J$-set, then for every
natural number $k$ the set of pairs $(a, d) \in \mathbb{N}^+ \times \mathbb{N}^+$ such that
$a + i d \in S$ for all $i = 0, 1, \dots, k$ is a $J$-set in $\mathbb{N}^+ \times \mathbb{N}^+$.

The paper writes $\mathbb{N}$ for the positive integers and takes $k \ge 1$; the case $k = 0$ is
included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 2 (`integers-2025-A4-thm-2`). -/
public theorem_wanted IsJSet.arithmeticProgressions_pnat {S : Set ℕ+} (hS : IsJSet S) (k : ℕ) :
    IsJSet {p : ℕ+ × ℕ+ | ∀ i ≤ k, (· + p.2)^[i] p.1 ∈ S}

/-- **Arithmetic progressions in essential CR-sets of the positive integers.** Let $\mathbb{N}^+$
denote the positive integers under addition. If $A \subseteq \mathbb{N}^+$ is an essential CR-set
and $l$ is a natural number, then the set of pairs $(a, b) \in \mathbb{N}^+ \times \mathbb{N}^+$
such that $a + i b \in A$ for all $i = 0, 1, \dots, l$ is an essential CR-set in
$\mathbb{N}^+ \times \mathbb{N}^+$.

The paper writes $\mathbb{N}$ for the positive integers and takes $l \ge 1$; the case $l = 0$ is
included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 9 (`integers-2025-A4-thm-9`). -/
public theorem_wanted IsEssentialCRSet.arithmeticProgressions_pnat {A : Set ℕ+}
    (hA : IsEssentialCRSet A) (l : ℕ) :
    IsEssentialCRSet {p : ℕ+ × ℕ+ | ∀ i ≤ l, (· + p.2)^[i] p.1 ∈ A}

end

end MetaMathlibExt
