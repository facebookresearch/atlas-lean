/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Hindman
public import Mathlib.Data.PNat.Basic

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

/-- A set `A` in a commutative semigroup is thick when every finite set has a
translate `E + x` inside `A`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of thick sets). -/
def IsAddThick (A : Set S) : Prop :=
  ∀ E : Finset S, ∃ x : S, ∀ e ∈ E, e + x ∈ A

/-- A set `A` is piecewise syndetic when for some finite `F` the union
`⋃ t ∈ F, -t + A` is thick, where `-t + A = {s | t + s ∈ A}`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of piecewise syndetic sets). -/
def IsAddPiecewiseSyndetic (A : Set S) : Prop :=
  ∃ F : Finset S, IsAddThick (⋃ t ∈ F, {s : S | t + s ∈ A})

/-- `A` is a `J`-set: for every finite family `F` of sequences `ℕ → S` there are
`a ∈ S` and a nonempty finite `H ⊆ ℕ` (a duplicate-free nonempty list) with
`a + ∑ n ∈ H, f n ∈ A` for every `f ∈ F`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 1. -/
def IsJSet (A : Set S) : Prop :=
  ∀ F : Finset (ℕ → S), ∃ a : S, ∃ H : List ℕ, H.Nodup ∧ H ≠ [] ∧
    ∀ f ∈ F, (H.map f).foldl (· + ·) a ∈ A

/-- `A` is a CR-set (combinatorially rich): for every `n` there is `r` such that for
every `r × n` matrix `M` over `S` there are a nonempty `α ⊆ {1, …, r}` and `s ∈ S`
with `s + ∑ i ∈ α, M i j ∈ A` for every column `j`.

The paper takes `n ≥ 1`. Allowing `n = 0` deliberately adds the requirement that `S` be
nonempty, the paper's implicit convention: over an empty `S` every `n ≥ 1` case holds vacuously
(take `r = 1`; there is no matrix), so without it `∅` would be a CR-set of the empty semigroup.
Over a nonempty `S` the two definitions agree.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 2. -/
def IsCRSet (A : Set S) : Prop :=
  ∀ n : ℕ, ∃ r : ℕ, ∀ M : Fin r → Fin n → S, ∃ α : Finset (Fin r), α.Nonempty ∧
    ∃ s : S, ∀ j, (α.toList.map fun i => M i j).foldl (· + ·) s ∈ A

/-- `A` is an essential CR-set: `A ∈ p` for an idempotent ultrafilter `p` all of
whose members are CR-sets, i.e. an idempotent of `β(CR)`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of essential CR-sets before Theorem 7). -/
def IsEssentialCRSet (A : Set S) : Prop :=
  ∃ p : Ultrafilter S, p + p = p ∧ (∀ B ∈ p, IsCRSet B) ∧ A ∈ p

/-- The whole semigroup is thick.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of thick sets). -/
theorem isAddThick_univ [Nonempty S] : IsAddThick (Set.univ : Set S) :=
  fun _ => ⟨Classical.arbitrary S, fun _ _ => Set.mem_univ _⟩

/-- The empty set is not thick in a nonempty semigroup.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of thick sets). -/
theorem not_isAddThick_empty [Nonempty S] : ¬ IsAddThick (∅ : Set S) := by
  intro h
  obtain ⟨x, hx⟩ := h {Classical.arbitrary S}
  exact hx _ (Finset.mem_singleton_self _)

/-- The whole semigroup is piecewise syndetic.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of piecewise syndetic sets). -/
theorem isAddPiecewiseSyndetic_univ [Nonempty S] :
    IsAddPiecewiseSyndetic (Set.univ : Set S) :=
  ⟨{Classical.arbitrary S}, fun _ => ⟨Classical.arbitrary S, fun _ _ => by simp⟩⟩

/-- The whole semigroup is a `J`-set.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 1. -/
theorem isJSet_univ [Nonempty S] : IsJSet (Set.univ : Set S) :=
  fun _ => ⟨Classical.arbitrary S, [0], List.nodup_singleton 0, List.cons_ne_nil _ _,
    fun _ _ => Set.mem_univ _⟩

/-- The whole semigroup is a CR-set.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 2. -/
theorem isCRSet_univ [Nonempty S] : IsCRSet (Set.univ : Set S) :=
  fun _ => ⟨1, fun _ => ⟨Finset.univ, Finset.univ_nonempty, Classical.arbitrary S,
    fun _ => Set.mem_univ _⟩⟩

/-- The empty set is not a CR-set.

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

/-- `F` is a family with the Ramsey property: a nonempty, upward hereditary
collection of nonempty subsets of `S` such that whenever `A ∪ B ∈ F`, one of `A`,
`B` lies in `F`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (families and the Ramsey property). -/
def IsRamseyFamily (F : Set (Set S)) : Prop :=
  F.Nonempty ∧ ∅ ∉ F ∧ (∀ A B, A ∈ F → A ⊆ B → B ∈ F) ∧
    ∀ A B, A ∪ B ∈ F → A ∈ F ∨ B ∈ F

/-- `β(F)`: the ultrafilters on `S` all of whose members lie in `F`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of `β(F)`). -/
def betaFamily (F : Set (Set S)) : Set (Ultrafilter S) :=
  {p | ∀ A ∈ p, A ∈ F}

/-- Membership in `β(F)`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of `β(F)`). -/
theorem mem_betaFamily {F : Set (Set S)} {p : Ultrafilter S} :
    p ∈ betaFamily F ↔ ∀ A ∈ p, A ∈ F :=
  Iff.rfl

/-- `β` of all nonempty subsets is all of `βS`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of `β(F)`). -/
theorem betaFamily_nonempty_sets :
    betaFamily {A : Set S | A.Nonempty} = Set.univ :=
  Set.eq_univ_of_forall fun _ _ hA => Ultrafilter.nonempty_of_mem hA

/-- **Theorem 3, part 1.** For a family `F` with the Ramsey property, `β(F)` is
closed in `βS`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
public theorem_wanted isClosed_betaFamily {F : Set (Set S)} (hF : IsRamseyFamily F) :
    IsClosed (betaFamily F)

/-- **Theorem 3, part 2.** For a family `F` with the Ramsey property,
`F = ⋃ β(F)`: a set lies in `F` iff it belongs to some ultrafilter in `β(F)`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
public theorem_wanted mem_iff_exists_mem_betaFamily {F : Set (Set S)} (hF : IsRamseyFamily F)
    (A : Set S) : A ∈ F ↔ ∃ p ∈ betaFamily F, A ∈ p

/-- **Theorem 3, part 3.** For a nonempty closed `K ⊆ βS`, the family
`F_K = {E | Ē ∩ K ≠ ∅}` (sets belonging to some member of `K`) has the Ramsey
property and `β(F_K) = K`.

The paper omits `K ≠ ∅`; for `K = ∅` the collection `F_K` is empty, hence not a
family.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
public theorem_wanted isRamseyFamily_and_betaFamily_eq_of_isClosed {K : Set (Ultrafilter S)}
    (hK : IsClosed K) (hne : K.Nonempty) :
    IsRamseyFamily {E : Set S | ∃ p ∈ K, E ∈ p} ∧ betaFamily {E : Set S | ∃ p ∈ K, E ∈ p} = K

/-- **Theorem 3, part 4.** In a semigroup `S`, if `β(F)` is a subsemigroup of `βS`
for a family `F` with the Ramsey property, then `β(F)` contains an idempotent.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
public theorem_wanted exists_idempotent_mem_betaFamily [Semigroup S] {F : Set (Set S)}
    (hF : IsRamseyFamily F) (hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) :
    ∃ p ∈ betaFamily F, p * p = p

/-- **Theorem 4 (left half).** For a family `F` with the Ramsey property in a
semigroup `S`, `β(F)` is a left ideal of `βS` iff `F` is left shift-invariant
(`s E ∈ F` for all `s ∈ S`, `E ∈ F`).

The paper's second sentence (right ideal iff right shift-invariant) is omitted: with
the paper's right topological convention it fails. For a minimal left ideal `L` of
`βℕ`, `F_L` is shift-invariant (left half, `ℕ` commutative), yet `L` is not a right
ideal, since a two-sided ideal contains `K(βℕ)`, a union of more than one minimal
left ideal.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 4 (`integers-2025-A4-thm-4`). -/
public theorem_wanted betaFamily_isLeftIdeal_iff [Semigroup S] {F : Set (Set S)}
    (hF : IsRamseyFamily F) :
    (∀ p : Ultrafilter S, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) ↔
      ∀ s : S, ∀ E ∈ F, (fun e => s * e) '' E ∈ F

/-- **Theorem 5.** For a family `F` with the Ramsey property in a semigroup `S`,
`β(F)` is a subsemigroup of `βS` iff: whenever `E ⊆ S` and some `A ∈ F` has
`⋂ x ∈ H, x⁻¹ E ∈ F` for every finite `H ⊆ A`, then `E ∈ F`. Here
`x⁻¹ E = {y | x * y ∈ E}`.

The record's `⋂ q ∈ H x⁻¹ E` is read as `⋂ x ∈ H, x⁻¹ E`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 5 (`integers-2025-A4-thm-5`). -/
public theorem_wanted betaFamily_isSubsemigroup_iff [Semigroup S] {F : Set (Set S)}
    (hF : IsRamseyFamily F) :
    (∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) ↔
      ∀ E : Set S, (∃ A ∈ F, ∀ H : Finset S, ↑H ⊆ A →
        (⋂ x ∈ H, {y : S | x * y ∈ E}) ∈ F) → E ∈ F

/-- **Theorem 6, (d) ⇒ (a).** Let `F` be a family with the Ramsey property in a
semigroup `S` with `β(F)` a subsemigroup. If a decreasing sequence `C n ⊆ A` of
members of `F` has, for each `n` and `x ∈ C n`, some `m` with `C m ⊆ x⁻¹ C n`, then
`A` is an essential `F`-set (a member of an idempotent of `β(F)`).

Statements (b) (trees of functions) and (c) (downward directed families) of the
paper are omitted. The sequence is indexed from `0` rather than `1`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 6 (`integers-2025-A4-thm-6`). -/
public theorem_wanted exists_idempotent_mem_of_decreasing_sequence [Semigroup S]
    {F : Set (Set S)} (hF : IsRamseyFamily F)
    (hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) {A : Set S}
    (C : ℕ → Set S) (hanti : Antitone C) (hCA : ∀ n, C n ⊆ A)
    (hshift : ∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : S | x * y ∈ C n}) (hCF : ∀ n, C n ∈ F) :
    ∃ p ∈ betaFamily F, p * p = p ∧ A ∈ p

/-- **Theorem 6, (a) ⇒ (d) for countable `S`.** With `F` as above and `S` countable,
every essential `F`-set `A` contains a decreasing sequence of members `C n ∈ F` such
that each `x ∈ C n` has some `m` with `C m ⊆ x⁻¹ C n`.

Statements (b) and (c) of the paper are omitted. The sequence is indexed from `0`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 6 (`integers-2025-A4-thm-6`). -/
public theorem_wanted exists_decreasing_sequence_of_idempotent_mem [Semigroup S] [Countable S]
    {F : Set (Set S)} (hF : IsRamseyFamily F)
    (hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) {A : Set S}
    (hA : ∃ p ∈ betaFamily F, p * p = p ∧ A ∈ p) :
    ∃ C : ℕ → Set S, Antitone C ∧ (∀ n, C n ⊆ A) ∧
      (∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : S | x * y ∈ C n}) ∧ ∀ n, C n ∈ F

end Families

/-- **Theorem 1** (Furstenberg–Glasner). If `S ⊆ ℤ` is piecewise syndetic, then for
every `k` the set of `(a, d) ∈ ℤ × ℤ` with `a, a + d, …, a + k d ∈ S` is piecewise
syndetic in `ℤ × ℤ`.

The paper takes `k ≥ 1`; `k = 0` is included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 1 (`integers-2025-A4-thm-1`). -/
public theorem_wanted IsAddPiecewiseSyndetic.arithmeticProgressions_int {S : Set ℤ}
    (hS : IsAddPiecewiseSyndetic S) (k : ℕ) :
    IsAddPiecewiseSyndetic {p : ℤ × ℤ | ∀ i ≤ k, p.1 + i * p.2 ∈ S}

/-- **Theorem 2** (Debnath–Goswami). If `S ⊆ ℕ` is a `J`-set, then for every `k` the
set of `(a, d) ∈ ℕ × ℕ` with `a, a + d, …, a + k d ∈ S` is a `J`-set in `ℕ × ℕ`.

The paper's `ℕ` is the positive integers, modelled by `ℕ+`; the paper takes
`k ≥ 1`, and `k = 0` is included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 2 (`integers-2025-A4-thm-2`). -/
public theorem_wanted IsJSet.arithmeticProgressions_pnat {S : Set ℕ+} (hS : IsJSet S) (k : ℕ) :
    IsJSet {p : ℕ+ × ℕ+ | ∀ i ≤ k, (· + p.2)^[i] p.1 ∈ S}

/-- **Theorem 7.** In a countable commutative semigroup `S`, a set `A` is an
essential CR-set iff it contains a decreasing sequence of CR-sets `C n` such that each
`x ∈ C n` has some `m` with `C m ⊆ -x + C n = {y | x + y ∈ C n}`.

The sequence is indexed from `0` rather than `1`.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 7 (`integers-2025-A4-thm-7`). -/
public theorem_wanted isEssentialCRSet_iff_exists_decreasing_sequence {S : Type*}
    [AddCommSemigroup S] [Countable S] (A : Set S) :
    IsEssentialCRSet A ↔ ∃ C : ℕ → Set S, Antitone C ∧ (∀ n, C n ⊆ A) ∧
      (∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : S | x + y ∈ C n}) ∧ ∀ n, IsCRSet (C n)

/-- **Theorem 8** (main theorem). If `A` is a CR-set in a commutative semigroup `S`
and `l ∈ ℕ`, then the set of `(a, b)` with `a, a + b, a + 2b, …, a + l b ∈ A` is a
CR-set in `S × S`.

The paper takes `l ≥ 1`; `l = 0` is included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 8 (`integers-2025-A4-thm-8`). -/
public theorem_wanted IsCRSet.arithmeticProgressions {S : Type*} [AddCommSemigroup S]
    {A : Set S} (hA : IsCRSet A) (l : ℕ) :
    IsCRSet {p : S × S | ∀ i ≤ l, (· + p.2)^[i] p.1 ∈ A}

/-- **Theorem 9.** If `A` is an essential CR-set in `ℕ` and `l ∈ ℕ`, then the set of
`(a, b)` with `a, a + b, …, a + l b ∈ A` is an essential CR-set in `ℕ × ℕ`.

The paper's `ℕ` is the positive integers, modelled by `ℕ+`; the paper takes
`l ≥ 1`, and `l = 0` is included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 9 (`integers-2025-A4-thm-9`). -/
public theorem_wanted IsEssentialCRSet.arithmeticProgressions_pnat {A : Set ℕ+}
    (hA : IsEssentialCRSet A) (l : ℕ) :
    IsEssentialCRSet {p : ℕ+ × ℕ+ | ∀ i ≤ l, (· + p.2)^[i] p.1 ∈ A}

end

end MetaMathlibExt
