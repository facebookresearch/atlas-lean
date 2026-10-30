/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Int.Interval
public import MathlibExt.Combinatorics.AP.Basic
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset

/-!
# Subset and subsequence sums with bounded numbers of terms (statements)

Statement-only targets from Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers
of Terms*, INTEGERS 24 (2024), Article A116.

* `boundedSubsetSums α β A` is `Σ^β_α(A)`, the sums of subsets `B ⊆ A` with
  `α ≤ |B| ≤ |A| - β`.
* `generalizedHFoldSumset a r h` is `h^{(r̄)}A` for the ordered set `A = {a₀, …, a_{k-1}}`.
* `yangChenBound r h` is `L(r̄, h)` (Section 1.1).
* A sequence `𝒜 = (A, t̄)` is the multiset `repetitionSequence a t` in which `a i` occurs `t i`
  times, and `boundedSubsequenceSums α β S` is `Σ^β_α(𝒜)`.

Ordered sets `a₀ < a₁ < ⋯` are strictly increasing maps out of `Fin k`; the set `A₀ = A ∪ {0}`
of the paper is `Fin.cons 0 b` (zero first) or `Fin.append c (Fin.cons 0 d)` (negative terms `c`,
zero, positive terms `d`).
-/

namespace MetaMathlibExt

@[expose] public section

open scoped Pointwise

/-- The generalized `h`-fold sumset `h^{(r̄)}A = {∑ sⱼ aⱼ : 0 ≤ sⱼ ≤ rⱼ, ∑ sⱼ = h}` of the
ordered set `A = {a₀, …, a_{k-1}}` (given as `a : Fin k → G`) with the tuple `r̄ = (r₀, …, r_{k-1})`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1 (definition of `h^{(r̄)}A`). -/
def generalizedHFoldSumset {G : Type*} [AddCommMonoid G] [DecidableEq G] {k : ℕ}
    (a : Fin k → G) (r : Fin k → ℕ) (h : ℕ) : Finset G :=
  ((Fintype.piFinset fun i => Finset.range (r i + 1)).filter fun s => ∑ i, s i = h).image
    fun s => ∑ i, s i • a i

/-- The bound `L(r̄, h)` of Yang and Chen: with `μ` the largest integer such that
`∑_{j<μ} rⱼ ≤ h`, `η` the least integer such that `∑_{j>η} rⱼ ≤ h`,
`δ = h - ∑_{j<μ} rⱼ` and `θ = h - ∑_{j>η} rⱼ`,
`L(r̄, h) = ∑_{j>η} j rⱼ - ∑_{j<μ} j rⱼ + θη - δμ + 1`.
Here `μ` is searched in `[0, k]` and `η + 1` is the least `m ∈ [0, k]` with `∑_{j ≥ m} rⱼ ≤ h`
(written `k - n` for the largest such `n`), so `η = -1` when `h = ∑ rⱼ`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1.1 (definitions of `μ`, `η`, `δ`, `θ` and `L(r̄, h)`). -/
def yangChenBound {k : ℕ} (r : Fin k → ℕ) (h : ℕ) : ℤ :=
  let pre : ℕ → ℕ := fun m => ∑ j : Fin k with j.val < m, r j
  let suf : ℕ → ℕ := fun m => ∑ j : Fin k with m ≤ j.val, r j
  let μ : ℕ := Nat.findGreatest (fun m => pre m ≤ h) k
  let m₀ : ℕ := k - Nat.findGreatest (fun n => suf (k - n) ≤ h) k
  let η : ℤ := (m₀ : ℤ) - 1
  let δ : ℤ := (h : ℤ) - pre μ
  let θ : ℤ := (h : ℤ) - suf m₀
  ((∑ j : Fin k with m₀ ≤ j.val, (j.val : ℤ) * r j) - ∑ j : Fin k with j.val < μ, (j.val : ℤ) * r j)
    + θ * η - δ * μ + 1

/-- `L((1, 1, 1), 2) = 3`: here `μ = 2`, `η = 0`, `δ = θ = 0`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1.1 (definition of `L(r̄, h)`). -/
theorem yangChenBound_one_one_one_two : yangChenBound (fun _ : Fin 3 => 1) 2 = 3 := by
  decide

/-- `L((1, 1, 2), 2) = 4`: here `μ = 2`, `η = 1`, `δ = θ = 0`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1.1 (definition of `L(r̄, h)`). -/
theorem yangChenBound_one_one_two_two : yangChenBound ![1, 1, 2] 2 = 4 := by
  decide

/-- `2^{(1,1,1)}{0, 1, 2} = {1, 2, 3}`, of size `L((1, 1, 1), 2) = 3`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1 (definition of `h^{(r̄)}A`). -/
theorem generalizedHFoldSumset_zero_one_two :
    generalizedHFoldSumset ![(0 : ℤ), 1, 2] (fun _ => 1) 2 = {1, 2, 3} := by
  decide

/-- The set `Σ^β_α(A) = {σ(B) : B ⊆ A, α ≤ |B| ≤ |A| - β}` of subset sums with at least `α` and
at most `|A| - β` terms, as the union of the restricted sumsets `m^∧A` for `α ≤ m ≤ |A| - β`
(the paper assumes `α + β ≤ |A|`).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1 (definition of `Σ^β_α(A)`). -/
def boundedSubsetSums {G : Type*} [AddCommMonoid G] [DecidableEq G] (α β : ℕ)
    (A : Finset G) : Finset G :=
  (Finset.Icc α (A.card - β)).biUnion fun m => restrictedSumset m A

/-- `Σ^1_1({-1, 1, 2}) = {-1, 0, 1, 2, 3}`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1 (definition of `Σ^β_α(A)`). -/
theorem boundedSubsetSums_one_one_neg_one_one_two :
    boundedSubsetSums 1 1 ({-1, 1, 2} : Finset ℤ) = {-1, 0, 1, 2, 3} := by
  decide

/-- The sequence `𝒜 = (A, t̄)` in which the term `a i` occurs `t i` times, as a multiset.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 4 (notation `(A, t̄)` for a finite sequence). -/
def repetitionSequence {G : Type*} {k : ℕ} (a : Fin k → G) (t : Fin k → ℕ) : Multiset G :=
  ∑ i, Multiset.replicate (t i) (a i)

/-- The length of `(A, t̄)` is `t₀ + ⋯ + t_{k-1}`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 4 (notation `(A, t̄)` for a finite sequence). -/
theorem card_repetitionSequence {G : Type*} {k : ℕ} (a : Fin k → G) (t : Fin k → ℕ) :
    Multiset.card (repetitionSequence a t) = ∑ i, t i := by
  simp [repetitionSequence]

/-- The set `Σ^β_α(𝒜) = {σ(ℬ) : ℬ ⊆ 𝒜, α ≤ |ℬ| ≤ |𝒜| - β}` of subsequence sums of the
sequence `𝒜` (a multiset) with at least `α` and at most `|𝒜| - β` terms.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 4 (definition of `Σ^β_α(𝒜)`). -/
def boundedSubsequenceSums {G : Type*} [AddCommMonoid G] [DecidableEq G] (α β : ℕ)
    (S : Multiset G) : Finset G :=
  ((S.powerset.filter fun T => α ≤ Multiset.card T ∧ Multiset.card T + β ≤ Multiset.card S).map
    Multiset.sum).toFinset

/-- `Σ^1_1({-2, 7, 7}) = {-2, 5, 7, 14}`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 4 (definition of `Σ^β_α(𝒜)`). -/
theorem boundedSubsequenceSums_one_one_example :
    boundedSubsequenceSums 1 1 (repetitionSequence ![(-2 : ℤ), 7] ![1, 2]) = {-2, 5, 7, 14} := by
  decide

/-- The bound `L(α, β, A)` of Theorem 7 for a set with `n` negative and `p` positive elements,
`k = n + p`, defined by the six printed cases with `T(x) = x(x + 1)/2`; it is `0` outside them
(the cases cover all `1 ≤ α`, `α + β ≤ k - 1`, `1 ≤ n ≤ p`).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 7 (definition of `L(α, β, A)`). -/
def mixedSignSubsetSumBound (n p α β : ℕ) : ℤ :=
  let N : ℤ := n
  let P : ℤ := p
  let a : ℤ := α
  let b : ℤ := β
  let kb : ℤ := N + P - b
  let T : ℤ → ℤ := fun x => x * (x + 1) / 2
  let base : ℤ := T P + T N + 1
  if 1 ≤ a ∧ a < kb ∧ kb < N ∧ N ≤ P then base - T (b - N) - T (b - P)
  else if (1 ≤ a ∧ a < N ∧ N ≤ kb ∧ kb < P) ∨ (1 ≤ a ∧ a = N ∧ N < kb ∧ kb ≤ P) then
    base - T (b - N)
  else if (1 ≤ a ∧ a < N ∧ N ≤ P ∧ P ≤ kb) ∨ (1 ≤ a ∧ a = N ∧ N < P ∧ P < kb) ∨
      (1 ≤ a ∧ a = N ∧ N = P ∧ P < kb) then base
  else if 1 ≤ N ∧ N < a ∧ a < kb ∧ kb ≤ P then base - T (b - N) - T (a - N)
  else if (1 ≤ N ∧ N < a ∧ a < P ∧ P < kb) ∨ (1 ≤ N ∧ N < a ∧ a = P ∧ P < kb) then
    base - T (a - N)
  else if 1 ≤ N ∧ N ≤ P ∧ P < a ∧ a < kb then base - T (a - N) - T (a - P)
  else 0

/-- `L(1, 1, A) = 5` for `n = 1`, `p = 2` (second case), attained by `A = {-1, 1, 2}`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 7 (definition of `L(α, β, A)`). -/
theorem mixedSignSubsetSumBound_one_two_one_one : mixedSignSubsetSumBound 1 2 1 1 = 5 := by
  decide

/-- The bound `L₀(α, β, A)` of Theorem 8 for a set with `n` negative elements, `p` positive
elements and `0`, `k = n + p + 1`, defined by the six printed cases with `T(x) = x(x + 1)/2` and
`T₀(x) = x(x - 1)/2`; it is `0` outside them (the cases cover all `1 ≤ α`, `α + β ≤ k - 1`,
`1 ≤ n ≤ p`).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 8 (definition of `L₀(α, β, A)`). -/
def mixedSignZeroSubsetSumBound (n p α β : ℕ) : ℤ :=
  let N : ℤ := n
  let P : ℤ := p
  let a : ℤ := α
  let b : ℤ := β
  let kb : ℤ := N + P + 1 - b
  let T : ℤ → ℤ := fun x => x * (x + 1) / 2
  let T₀ : ℤ → ℤ := fun x => x * (x - 1) / 2
  let base : ℤ := T P + T N + 1
  if 1 ≤ a ∧ a < kb ∧ kb < N ∧ N ≤ P then base - T₀ (b - N) - T₀ (b - P)
  else if (1 ≤ a ∧ a < N ∧ N ≤ kb ∧ kb < P) ∨ (1 ≤ a ∧ a = N ∧ N < kb ∧ kb ≤ P) then
    base - T₀ (b - N)
  else if (1 ≤ a ∧ a < N ∧ N ≤ P ∧ P ≤ kb) ∨ (1 ≤ a ∧ a = N ∧ N < P ∧ P < kb) ∨
      (1 ≤ a ∧ a = N ∧ N = P ∧ P < kb) then base
  else if 1 ≤ N ∧ N < a ∧ a < kb ∧ kb ≤ P then base - T₀ (b - N) - T₀ (a - N)
  else if (1 ≤ N ∧ N < a ∧ a < P ∧ P < kb) ∨ (1 ≤ N ∧ N < a ∧ a = P ∧ P < kb) then
    base - T₀ (a - N)
  else if 1 ≤ N ∧ N ≤ P ∧ P < a ∧ a < kb then base - T₀ (a - N) - T₀ (a - P)
  else 0

/-- `L₀(1, 1, A) = 3` for `n = p = 1` (third case), attained by `A = {-1, 0, 1}`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 8 (definition of `L₀(α, β, A)`). -/
theorem mixedSignZeroSubsetSumBound_one_one_one_one :
    mixedSignZeroSubsetSumBound 1 1 1 1 = 3 := by
  decide

/-! ## The generalized `h`-fold sumset (Yang and Chen) -/

/-- Yang–Chen direct theorem: for integers `a₀ < ⋯ < a_{k-1}`, positive `r̄` and
`2 ≤ h ≤ ∑ rⱼ`, `|h^{(r̄)}A| ≥ L(r̄, h)`, and the bound is attained.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 2 (Yang and Chen) (`integers-2024-A116-thm-2`). -/
public theorem_wanted yangChen_card_generalizedHFoldSumset_ge {k : ℕ} (r : Fin k → ℕ)
    (hr : ∀ i, 0 < r i) (h : ℕ) (hh : 2 ≤ h) (hhr : h ≤ ∑ i, r i) :
    (∀ a : Fin k → ℤ, StrictMono a →
      yangChenBound r h ≤ (generalizedHFoldSumset a r h).card) ∧
    ∃ a : Fin k → ℤ, StrictMono a ∧
      ((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h

/-- Yang–Chen inverse theorem for `k ≥ 5`: if `2 ≤ h ≤ ∑ rⱼ - 2`, then
`|h^{(r̄)}A| = L(r̄, h)` if and only if `A` is a `k`-term arithmetic progression
(`A` listed increasingly, as in Theorem 2).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 3 (Yang and Chen) (`integers-2024-A116-thm-3`). -/
public theorem_wanted yangChen_card_generalizedHFoldSumset_eq_iff_isAP {k : ℕ} (hk : 5 ≤ k)
    (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (h : ℕ) (hh : 2 ≤ h) (hhr : h + 2 ≤ ∑ i, r i)
    (a : Fin k → ℤ) (ha : StrictMono a) :
    ((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h ↔
      (Set.range a).IsAPOfLength k

/-- Yang–Chen inverse theorem for `k = 3`: if `2 ≤ h ≤ r₀ + r₁ + r₂ - 2`, then
`|h^{(r̄)}A| = L(r̄, h)` always when `r₁ = 1`, and if and only if `A` is a `3`-term arithmetic
progression when `r₁ ≥ 2`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 4 (Yang and Chen) (`integers-2024-A116-thm-4`). -/
public theorem_wanted yangChen_card_generalizedHFoldSumset_eq_three (a : Fin 3 → ℤ)
    (ha : StrictMono a) (r : Fin 3 → ℕ) (hr : ∀ i, 0 < r i) (h : ℕ) (hh : 2 ≤ h)
    (hhr : h + 2 ≤ r 0 + r 1 + r 2) :
    (r 1 = 1 → ((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h) ∧
    (2 ≤ r 1 → (((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h ↔
      (Set.range a).IsAPOfLength 3))

/-- Yang–Chen inverse theorem for `k = 4`: if `2 ≤ h ≤ r₀ + r₁ + r₂ + r₃ - 2`, then for
`r₁ = r₂ = 1`, `|h^{(r̄)}A| = L(r̄, h)` if and only if `a₁ - a₀ = a₃ - a₂`, and for `r₁ ≥ 2` or
`r₂ ≥ 2` if and only if `A` is a `4`-term arithmetic progression.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 5 (Yang and Chen) (`integers-2024-A116-thm-5`). -/
public theorem_wanted yangChen_card_generalizedHFoldSumset_eq_four (a : Fin 4 → ℤ)
    (ha : StrictMono a) (r : Fin 4 → ℕ) (hr : ∀ i, 0 < r i) (h : ℕ) (hh : 2 ≤ h)
    (hhr : h + 2 ≤ r 0 + r 1 + r 2 + r 3) :
    (r 1 = 1 → r 2 = 1 → (((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h ↔
      a 1 - a 0 = a 3 - a 2)) ∧
    (2 ≤ r 1 ∨ 2 ≤ r 2 → (((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h ↔
      (Set.range a).IsAPOfLength 4))

/-! ## Subset sums as generalized `h`-fold sumsets -/

/-- For `A = {a₁, …, a_k} ⊆ G` with `0 ∉ A` and `α + β ≤ k - 1`,
`Σ^β_α(A) = (k - β)^{(r̄)}A₀` with `A₀ = {0, a₁, …, a_k}` and `r̄ = (k - α - β, 1, …, 1)`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 1 (`integers-2024-A116-lem-1`). -/
public theorem_wanted boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_not_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {k : ℕ} (b : Fin k → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (α β : ℕ) (hαβ : α + β + 1 ≤ k) :
    boundedSubsetSums α β (Finset.univ.image b) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (k + 1) → G)
        (Fin.cons (k - α - β) fun _ => 1 : Fin (k + 1) → ℕ) (k - β)

/-- For `A = {0, a₁, …, a_{k-1}} ⊆ G` with `k` distinct elements, `1 ≤ α ≤ k`, `β ≤ k - 1` and
`α + β ≤ k`, `Σ^β_α(A) = (k - β)^{(r̄)}A` with `r̄ = (k - α - β + 1, 1, …, 1)`; here `k = m + 1`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 2 (`integers-2024-A116-lem-2`). -/
public theorem_wanted boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {m : ℕ} (b : Fin m → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (α β : ℕ) (hα : 1 ≤ α) (hβ : β ≤ m)
    (hαβ : α + β ≤ m + 1) :
    boundedSubsetSums α β (Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → G)) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (m + 1) → G)
        (Fin.cons (m + 1 - α - β + 1) fun _ => 1 : Fin (m + 1) → ℕ) (m + 1 - β)

/-- Reordering: `h^{(r̄)}A = h^{(r̄_π)}A_π` for every permutation `π` of the indices (stated
for every `h`, tuple `r̄` and indexing `a`; the paper assumes `h ≥ 2`, `r̄` positive and `A` a set).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 3 (`integers-2024-A116-lem-3`). -/
public theorem_wanted generalizedHFoldSumset_comp_perm {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {k : ℕ} (a : Fin k → G) (r : Fin k → ℕ) (h : ℕ) (π : Equiv.Perm (Fin k)) :
    generalizedHFoldSumset (a ∘ π) (r ∘ π) h = generalizedHFoldSumset a r h

/-- For a sequence `𝒜 = (A, t̄)` with `A = {a₁, …, a_k}`, `0 ∉ A`, positive `t̄`,
`h = t₁ + ⋯ + t_k`, `1 ≤ α` and `α + β ≤ h - 1`,
`Σ^β_α(𝒜) = (h - β)^{(r̄)}A₀` with `A₀ = {0, a₁, …, a_k}` and `r̄ = (h - α - β, t₁, …, t_k)`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 4 (`integers-2024-A116-lem-4`). -/
public theorem_wanted boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_not_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {k : ℕ} (b : Fin k → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (t : Fin k → ℕ) (ht : ∀ i, 0 < t i)
    (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ h) :
    boundedSubsequenceSums α β (repetitionSequence b t) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (k + 1) → G)
        (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β)

/-- For a sequence `𝒜 = (A, t̄)` with `A = {0, a₁, …, a_{k-1}}` (distinct terms), positive
`t̄ = (t₀, …, t_{k-1})`, `h = t₀ + ⋯ + t_{k-1}`, `1 ≤ α`, `β ≤ h - 1` and `α + β ≤ h`,
`Σ^β_α(𝒜) = (h - β)^{(r̄)}A` with `r̄ = (h - α - β + t₀, t₁, …, t_{k-1})`; here `k = m + 1`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 5 (`integers-2024-A116-lem-5`). -/
public theorem_wanted boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {m : ℕ} (b : Fin m → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (t : Fin (m + 1) → ℕ) (ht : ∀ i, 0 < t i)
    (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α) (hβ : β + 1 ≤ h) (hαβ : α + β ≤ h) :
    boundedSubsequenceSums α β (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → G) t) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (m + 1) → G)
        (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β)

/-! ## Direct and inverse theorems for subset sums -/

/-- For `k ≥ 2`, `1 ≤ α` and `α + β ≤ k - 1`: a set `A` of `k` positive integers has
`|Σ^β_α(A)| ≥ k(k+1)/2 - α(α+1)/2 - β(β+1)/2 + 1`, a set of `k` nonnegative integers containing
`0` has `|Σ^β_α(A)| ≥ k(k-1)/2 - α(α-1)/2 - β(β-1)/2 + 1`, and both bounds are attained (by
`[1, k]` and `[0, k - 1]`, the witnesses named in the proof).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 6 (`integers-2024-A116-thm-6`). -/
public theorem_wanted card_boundedSubsetSums_ge_of_nonneg (k α β : ℕ) (hk : 2 ≤ k)
    (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ k) :
    (∀ A : Finset ℤ, A.card = k → (∀ x ∈ A, 0 < x) →
      ((k + 1).choose 2 : ℤ) - (α + 1).choose 2 - (β + 1).choose 2 + 1 ≤
        (boundedSubsetSums α β A).card) ∧
    (∀ A : Finset ℤ, A.card = k → (∀ x ∈ A, 0 ≤ x) → 0 ∈ A →
      (k.choose 2 : ℤ) - α.choose 2 - β.choose 2 + 1 ≤ (boundedSubsetSums α β A).card) ∧
    ((boundedSubsetSums α β (Finset.Icc 1 (k : ℤ))).card : ℤ) =
      ((k + 1).choose 2 : ℤ) - (α + 1).choose 2 - (β + 1).choose 2 + 1 ∧
    ((boundedSubsetSums α β (Finset.Icc 0 ((k : ℤ) - 1))).card : ℤ) =
      (k.choose 2 : ℤ) - α.choose 2 - β.choose 2 + 1

/-- For a set `A` of `p` positive and `n` negative integers, `1 ≤ n ≤ p`, `k = n + p`, `1 ≤ α`
and `α + β ≤ k - 1`: `|Σ^β_α(A)| ≥ L(α, β, A)`, and the bound is attained.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 7 (`integers-2024-A116-thm-7`). -/
public theorem_wanted card_boundedSubsetSums_ge_mixedSign (n p α β : ℕ) (hn : 1 ≤ n)
    (hnp : n ≤ p) (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ n + p) :
    (∀ A : Finset ℤ, 0 ∉ A → (A.filter (· < 0)).card = n → (A.filter (0 < ·)).card = p →
      mixedSignSubsetSumBound n p α β ≤ (boundedSubsetSums α β A).card) ∧
    ∃ A : Finset ℤ, 0 ∉ A ∧ (A.filter (· < 0)).card = n ∧ (A.filter (0 < ·)).card = p ∧
      ((boundedSubsetSums α β A).card : ℤ) = mixedSignSubsetSumBound n p α β

/-- For a set `A` of `p` positive integers, `n` negative integers and `0`, `1 ≤ n ≤ p`,
`k = n + p + 1`, `1 ≤ α` and `α + β ≤ k - 1`: `|Σ^β_α(A)| ≥ L₀(α, β, A)`, and the bound is
attained.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 8 (`integers-2024-A116-thm-8`). -/
public theorem_wanted card_boundedSubsetSums_ge_mixedSign_zero (n p α β : ℕ) (hn : 1 ≤ n)
    (hnp : n ≤ p) (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ n + p + 1) :
    (∀ A : Finset ℤ, 0 ∈ A → (A.filter (· < 0)).card = n → (A.filter (0 < ·)).card = p →
      mixedSignZeroSubsetSumBound n p α β ≤ (boundedSubsetSums α β A).card) ∧
    ∃ A : Finset ℤ, 0 ∈ A ∧ (A.filter (· < 0)).card = n ∧ (A.filter (0 < ·)).card = p ∧
      ((boundedSubsetSums α β A).card : ℤ) = mixedSignZeroSubsetSumBound n p α β

/-- Inverse theorem for Theorem 6 (`k ≥ 3`, `1 ≤ α ≤ k - 2`, `β ≤ k - 2`, `α + β ≤ k - 1`):
if a set of `k` positive integers attains the bound, then `A = d · [1, k]` with `d > 0`, except
for `k = 3`, where `A = {a₁, a₂, a₁ + a₂}` with `0 < a₁ < a₂`; if a set of `k` nonnegative
integers containing `0` attains its bound, then `A = d · [0, k - 1]`, except for `k = 3`
(`A = {0, a₁, a₂}`) and `k = 4` (`A = {0, a₁, a₂, a₁ + a₂}`), where `0 < a₁ < a₂`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 9 (`integers-2024-A116-thm-9`). -/
public theorem_wanted boundedSubsetSums_inverse_of_nonneg (A : Finset ℤ) (k α β : ℕ)
    (hk : 3 ≤ k) (hA : A.card = k) (hα : 1 ≤ α) (hα2 : α + 2 ≤ k) (hβ : β + 2 ≤ k)
    (hαβ : α + β + 1 ≤ k) :
    ((∀ x ∈ A, 0 < x) → ((boundedSubsetSums α β A).card : ℤ) =
        ((k + 1).choose 2 : ℤ) - (α + 1).choose 2 - (β + 1).choose 2 + 1 →
      (k ≠ 3 → ∃ d : ℤ, 0 < d ∧ A = d • Finset.Icc 1 (k : ℤ)) ∧
      (k = 3 → ∃ x y : ℤ, 0 < x ∧ x < y ∧ A = {x, y, x + y})) ∧
    ((∀ x ∈ A, 0 ≤ x) → 0 ∈ A → ((boundedSubsetSums α β A).card : ℤ) =
        (k.choose 2 : ℤ) - α.choose 2 - β.choose 2 + 1 →
      (5 ≤ k → ∃ d : ℤ, 0 < d ∧ A = d • Finset.Icc 0 ((k : ℤ) - 1)) ∧
      (k = 3 → ∃ x y : ℤ, 0 < x ∧ x < y ∧ A = {0, x, y}) ∧
      (k = 4 → ∃ x y : ℤ, 0 < x ∧ x < y ∧ A = {0, x, y, x + y}))

/-- Inverse theorem for Theorem 7 (`p` positive and `n` negative integers, `1 ≤ n ≤ p`,
`k = n + p`, `1 ≤ α ≤ k - 2`, `β ≤ k - 2`, `α + β ≤ k - 1`): (i) for `k = 3`, `α = 1`, `β = 0`,
`|Σ^β_α(A)| = L(α, β, A)` iff `A = d · {-1, 1, 2}`; (ii) for `k = 3`, `α = β = 1`, iff
`A = {a₀, a₀ + a₃, a₃}` with `a₀ < 0 < a₀ + a₃ < a₃`; (iii) for `k ≥ 4`, iff
`A = d · {-n, …, -1, 1, …, p}`. Here `d > 0` (necessarily the least positive element of `A`).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 10 (`integers-2024-A116-thm-10`). -/
public theorem_wanted boundedSubsetSums_inverse_mixedSign (A : Finset ℤ) (n p α β : ℕ)
    (hA0 : 0 ∉ A) (hneg : (A.filter (· < 0)).card = n) (hpos : (A.filter (0 < ·)).card = p)
    (hn : 1 ≤ n) (hnp : n ≤ p) (hα : 1 ≤ α) (hα2 : α + 2 ≤ n + p) (hβ : β + 2 ≤ n + p)
    (hαβ : α + β + 1 ≤ n + p) :
    (n + p = 3 → α = 1 → β = 0 →
      (((boundedSubsetSums α β A).card : ℤ) = mixedSignSubsetSumBound n p α β ↔
        ∃ d : ℤ, 0 < d ∧ A = d • ({-1, 1, 2} : Finset ℤ))) ∧
    (n + p = 3 → α = 1 → β = 1 →
      (((boundedSubsetSums α β A).card : ℤ) = mixedSignSubsetSumBound n p α β ↔
        ∃ x y : ℤ, x < 0 ∧ 0 < x + y ∧ x + y < y ∧ A = {x, x + y, y})) ∧
    (4 ≤ n + p →
      (((boundedSubsetSums α β A).card : ℤ) = mixedSignSubsetSumBound n p α β ↔
        ∃ d : ℤ, 0 < d ∧ A = d • (Finset.Icc (-(n : ℤ)) p).erase 0))

/-- Inverse theorem for Theorem 8 (`p` positive integers, `n` negative integers and `0`,
`1 ≤ n ≤ p`, `k = n + p + 1`, `1 ≤ α ≤ k - 2`, `β ≤ k - 2`, `α + β ≤ k - 1`):
`|Σ^β_α(A)| = L₀(α, β, A)` iff `A = d · [-n, p]` with `d > 0` (necessarily the least positive
element of `A`).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 11 (`integers-2024-A116-thm-11`). -/
public theorem_wanted boundedSubsetSums_inverse_mixedSign_zero (A : Finset ℤ) (n p α β : ℕ)
    (hA0 : 0 ∈ A) (hneg : (A.filter (· < 0)).card = n) (hpos : (A.filter (0 < ·)).card = p)
    (hn : 1 ≤ n) (hnp : n ≤ p) (hα : 1 ≤ α) (hα2 : α + 2 ≤ n + p + 1) (hβ : β + 2 ≤ n + p + 1)
    (hαβ : α + β + 1 ≤ n + p + 1) :
    ((boundedSubsetSums α β A).card : ℤ) = mixedSignZeroSubsetSumBound n p α β ↔
      ∃ d : ℤ, 0 < d ∧ A = d • Finset.Icc (-(n : ℤ)) p

/-! ## Direct theorems for subsequence sums -/

/-- For `k ≥ 2` positive integers `0 < a₁ < ⋯ < a_k` with positive multiplicities `t̄`,
`h = t₁ + ⋯ + t_k`, `1 ≤ α` and `α + β ≤ h - 1`: `|Σ^β_α(𝒜)| ≥ L(r̄, h - β)` with
`r̄ = (h - α - β, t₁, …, t_k)`, and the bound is attained.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 13 (`integers-2024-A116-thm-13`). -/
public theorem_wanted card_boundedSubsequenceSums_ge_of_pos {k : ℕ} (hk : 2 ≤ k)
    (t : Fin k → ℕ) (ht : ∀ i, 0 < t i) (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α)
    (hαβ : α + β + 1 ≤ h) :
    (∀ b : Fin k → ℤ, StrictMono b → (∀ i, 0 < b i) →
      yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ≤
        (boundedSubsequenceSums α β (repetitionSequence b t)).card) ∧
    ∃ b : Fin k → ℤ, StrictMono b ∧ (∀ i, 0 < b i) ∧
      ((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
        yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β)

/-- For `k ≥ 2` integers `0 = a₀ < a₁ < ⋯ < a_{k-1}` with positive multiplicities `t̄`,
`h = t₀ + ⋯ + t_{k-1}`, `1 ≤ α`, `β ≤ h - 1` and `α + β ≤ h`: `|Σ^β_α(𝒜)| ≥ L(r̄, h - β)`
with `r̄ = (h - α - β + t₀, t₁, …, t_{k-1})`, and the bound is attained; here `k = m + 1`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 14 (`integers-2024-A116-thm-14`). -/
public theorem_wanted card_boundedSubsequenceSums_ge_of_nonneg_zero {m : ℕ} (hm : 1 ≤ m)
    (t : Fin (m + 1) → ℕ) (ht : ∀ i, 0 < t i) (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ)
    (hα : 1 ≤ α) (hβ : β + 1 ≤ h) (hαβ : α + β ≤ h) :
    (∀ b : Fin m → ℤ, StrictMono b → (∀ i, 0 < b i) →
      yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ≤
        (boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card) ∧
    ∃ b : Fin m → ℤ, StrictMono b ∧ (∀ i, 0 < b i) ∧
      ((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
        yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β)

/-- For `n` negative terms `a₀ < ⋯ < a_{n-1} < 0` and `p` positive terms
`0 < a_{n+1} < ⋯ < a_{n+p}` (`1 ≤ n ≤ p`) with positive multiplicities, `h` the length,
`1 ≤ α` and `α + β ≤ h - 1`: `|Σ^β_α(𝒜)| ≥ L(r̄, h - β)` with
`r̄ = (t₀, …, t_{n-1}, h - α - β, t_{n+1}, …, t_{n+p})` on `A₀ = A ∪ {0}`, and the bound is
attained. Negative terms are `c`, positive terms `d`.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 15 (`integers-2024-A116-thm-15`). -/
public theorem_wanted card_boundedSubsequenceSums_ge_mixedSign {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) (tn : Fin n → ℕ) (tp : Fin p → ℕ) (htn : ∀ i, 0 < tn i)
    (htp : ∀ j, 0 < tp j) (h : ℕ) (hh : h = ∑ i, tn i + ∑ j, tp j) (α β : ℕ) (hα : 1 ≤ α)
    (hαβ : α + β + 1 ≤ h) :
    (∀ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c → (∀ i, c i < 0) → StrictMono d →
      (∀ j, 0 < d j) →
      yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β) ≤
        (boundedSubsequenceSums α β (repetitionSequence c tn + repetitionSequence d tp)).card) ∧
    ∃ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c ∧ (∀ i, c i < 0) ∧ StrictMono d ∧
      (∀ j, 0 < d j) ∧
      ((boundedSubsequenceSums α β (repetitionSequence c tn + repetitionSequence d tp)).card :
          ℤ) = yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β)

/-- For `n` negative terms, the term `0` with multiplicity `t_n` and `p` positive terms
(`1 ≤ n ≤ p`), all multiplicities positive, `h` the length, `1 ≤ α` and `α + β ≤ h - 1`:
`|Σ^β_α(𝒜)| ≥ L(r̄, h - β)` with
`r̄ = (t₀, …, t_{n-1}, h - α - β + t_n, t_{n+1}, …, t_{n+p})`, and the bound is attained.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 16 (`integers-2024-A116-thm-16`). -/
public theorem_wanted card_boundedSubsequenceSums_ge_mixedSign_zero {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) (tn : Fin n → ℕ) (tz : ℕ) (tp : Fin p → ℕ) (htn : ∀ i, 0 < tn i)
    (htz : 0 < tz) (htp : ∀ j, 0 < tp j) (h : ℕ) (hh : h = ∑ i, tn i + tz + ∑ j, tp j)
    (α β : ℕ) (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ h) :
    (∀ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c → (∀ i, c i < 0) → StrictMono d →
      (∀ j, 0 < d j) →
      yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ≤
        (boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card) ∧
    ∃ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c ∧ (∀ i, c i < 0) ∧ StrictMono d ∧
      (∀ j, 0 < d j) ∧
      ((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
        yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β)

/-! ## Inverse theorems for subsequence sums -/

/-- Inverse theorem for Theorem 13 (`k ≥ 2`, `1 ≤ α ≤ h - 2`, `β ≤ h - 2`, `α + β ≤ h - 1`),
writing `E` for `|Σ^β_α(𝒜)| = L(r̄, h - β)`: (a) for `k = 2`, `E` holds when `t₁ = 1`, and for
`t₁ ≥ 2`, `E` iff `A = a₁ · [1, 2]`; (b) for `k = 3` and `t₁ = t₂ = 1`, `E` iff
`A = {a₁, a₂, a₁ + a₂}`, and for `t₁ ≥ 2` or `t₂ ≥ 2`, `E` iff `A = a₁ · [1, 3]`; (c) for
`k ≥ 4`, `E` iff `A = a₁ · [1, k]`. Dilations are by some `e > 0` (necessarily `a₁`).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 17 (`integers-2024-A116-thm-17`). -/
public theorem_wanted boundedSubsequenceSums_inverse_of_pos {k : ℕ} (hk : 2 ≤ k)
    (b : Fin k → ℤ) (hb : StrictMono b) (hbpos : ∀ i, 0 < b i) (t : Fin k → ℕ)
    (ht : ∀ i, 0 < t i) (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α) (hα2 : α + 2 ≤ h)
    (hβ : β + 2 ≤ h) (hαβ : α + β + 1 ≤ h) :
    (∀ hk2 : k = 2, t ⟨0, by omega⟩ = 1 →
      ((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
        yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β)) ∧
    (∀ hk2 : k = 2, 2 ≤ t ⟨0, by omega⟩ →
      (((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧ Finset.univ.image b = e • Finset.Icc 1 (2 : ℤ))) ∧
    (∀ hk3 : k = 3, t ⟨0, by omega⟩ = 1 → t ⟨1, by omega⟩ = 1 →
      (((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ↔
        ∃ x y : ℤ, 0 < x ∧ x < y ∧ Finset.univ.image b = {x, y, x + y})) ∧
    (∀ hk3 : k = 3, 2 ≤ t ⟨0, by omega⟩ ∨ 2 ≤ t ⟨1, by omega⟩ →
      (((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧ Finset.univ.image b = e • Finset.Icc 1 (3 : ℤ))) ∧
    (4 ≤ k →
      (((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧ Finset.univ.image b = e • Finset.Icc 1 (k : ℤ)))

/-- Inverse theorem for Theorem 14 (`k = m + 1 ≥ 3`, `0 = a₀ < a₁ < ⋯`, `1 ≤ α ≤ h - 2`,
`β ≤ h - 2`, `α + β ≤ h - 1`), writing `E` for `|Σ^β_α(𝒜)| = L(r̄, h - β)`: (a) for `k = 3`,
`E` holds when `t₁ = 1`, and for `t₁ ≥ 2`, `E` iff `A = a₁ · [0, 2]`; (b) for `k = 4` and
`t₁ = t₂ = 1`, `E` iff `A = {0, a₁, a₂, a₁ + a₂}`, and for `t₁ ≥ 2` or `t₂ ≥ 2`, `E` iff
`A = a₁ · [0, 3]`; (c) for `k ≥ 5`, `E` iff `A = a₁ · [0, k - 1]`. Dilations are by some
`e > 0` (necessarily `a₁`).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 18 (`integers-2024-A116-thm-18`). -/
public theorem_wanted boundedSubsequenceSums_inverse_of_nonneg_zero {m : ℕ} (hm : 2 ≤ m)
    (b : Fin m → ℤ) (hb : StrictMono b) (hbpos : ∀ i, 0 < b i) (t : Fin (m + 1) → ℕ)
    (ht : ∀ i, 0 < t i) (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α) (hα2 : α + 2 ≤ h)
    (hβ : β + 2 ≤ h) (hαβ : α + β + 1 ≤ h) :
    (m = 2 → t ⟨1, by omega⟩ = 1 →
      ((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
        yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β)) ∧
    (m = 2 → 2 ≤ t ⟨1, by omega⟩ →
      (((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → ℤ) = e • Finset.Icc 0 (2 : ℤ))) ∧
    (m = 3 → t ⟨1, by omega⟩ = 1 → t ⟨2, by omega⟩ = 1 →
      (((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ↔
        ∃ x y : ℤ, 0 < x ∧ x < y ∧
          Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → ℤ) = {0, x, y, x + y})) ∧
    (m = 3 → 2 ≤ t ⟨1, by omega⟩ ∨ 2 ≤ t ⟨2, by omega⟩ →
      (((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → ℤ) = e • Finset.Icc 0 (3 : ℤ))) ∧
    (4 ≤ m →
      (((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → ℤ) = e • Finset.Icc 0 (m : ℤ)))

/-- Inverse theorem for Theorem 15 (`1 ≤ n ≤ p`, `k = n + p`, `h ≥ 3`, `1 ≤ α ≤ h - 2`,
`β ≤ h - 2`, `α + β ≤ h - 1`), writing `E` for `|Σ^β_α(𝒜)| = L(r̄, h - β)`: (a) for `k = 3`,
`α + β = h - 1` and `t₂ = 1` (the multiplicity of the least positive term), `E` iff
`A = {a₂ - a₃, a₂, a₃}`; (b) in all other cases, `E` iff
`A = a_{n+1} · {-n, …, -1, 1, …, p}`. CORRECTED READING: (b) also excludes `k = 2` with
`α + β = h - 1`, where the proof's `r₁ = h - α - β ≥ 2` fails and Theorem 4(i) gives `E` for
every `A`: `A = {-2, 7}`, `t̄ = (1, 2)`, `α = β = 1` has `|Σ^1_1(𝒜)| = |{-2, 5, 7, 14}| = 4 = L`.
Dilations are by some `e > 0` (necessarily `a_{n+1}`).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 19 (`integers-2024-A116-thm-19`). -/
public theorem_wanted boundedSubsequenceSums_inverse_mixedSign {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) (c : Fin n → ℤ) (d : Fin p → ℤ) (hc : StrictMono c) (hcneg : ∀ i, c i < 0)
    (hd : StrictMono d) (hdpos : ∀ j, 0 < d j) (tn : Fin n → ℕ) (tp : Fin p → ℕ)
    (htn : ∀ i, 0 < tn i) (htp : ∀ j, 0 < tp j) (h : ℕ) (hh : h = ∑ i, tn i + ∑ j, tp j)
    (hh3 : 3 ≤ h) (α β : ℕ) (hα : 1 ≤ α) (hα2 : α + 2 ≤ h) (hβ : β + 2 ≤ h)
    (hαβ : α + β + 1 ≤ h) :
    (n + p = 3 → α + β + 1 = h → tp ⟨0, by omega⟩ = 1 →
      (((boundedSubsequenceSums α β
          (repetitionSequence c tn + repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β) ↔
        ∃ x y : ℤ, 0 < x ∧ x < y ∧ Finset.univ.image c ∪ Finset.univ.image d = {x - y, x, y})) ∧
    (¬ (n + p = 3 ∧ α + β + 1 = h ∧ tp ⟨0, by omega⟩ = 1) → ¬ (n + p = 2 ∧ α + β + 1 = h) →
      (((boundedSubsequenceSums α β
          (repetitionSequence c tn + repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          Finset.univ.image c ∪ Finset.univ.image d = e • (Finset.Icc (-(n : ℤ)) p).erase 0))

/-- Inverse theorem for Theorem 16 (`n` negative terms, `0` with multiplicity `t_n`, `p`
positive terms, `1 ≤ n ≤ p`, `k = n + p + 1`, `1 ≤ α ≤ h - 2`, `β ≤ h - 2`, `α + β ≤ h`),
writing `E` for `|Σ^β_α(𝒜)| = L(r̄, h - β)` with
`r̄ = (t₀, …, t_{n-1}, h - α - β + t_n, t_{n+1}, …, t_{n+p})`: (a) `k = 3`, `α + β = h`: `E`
holds when `t₁ = 1`, and for `t₁ ≥ 2`, `E` iff `A = a₂ · [-1, 1]`; (b) `k = 3`,
`α + β ≤ h - 1`: `E` iff `A = a₂ · [-1, 1]`; (c) `k = 4`, `α + β = h`: for `t₁ = t₂ = 1`, `E`
iff `A = {a₂ - a₃, 0, a₂, a₃}`, and for `t₁ ≥ 2` or `t₂ ≥ 2`, `E` iff `A = a₂ · [-1, 2]`;
(d) `k = 4`, `α + β ≤ h - 1`: `E` iff `A = a₂ · [-1, 2]`; (e) otherwise (`k ≥ 5`), `E` iff
`A = a_{n+1} · [-n, p]`. Here `t₁` is the multiplicity `t_n` of `0` and `t₂` that of the least
positive term; dilations are by some `e > 0` (necessarily the least positive term).

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 20 (`integers-2024-A116-thm-20`). -/
public theorem_wanted boundedSubsequenceSums_inverse_mixedSign_zero {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) (c : Fin n → ℤ) (d : Fin p → ℤ) (hc : StrictMono c) (hcneg : ∀ i, c i < 0)
    (hd : StrictMono d) (hdpos : ∀ j, 0 < d j) (tn : Fin n → ℕ) (tz : ℕ) (tp : Fin p → ℕ)
    (htn : ∀ i, 0 < tn i) (htz : 0 < tz) (htp : ∀ j, 0 < tp j) (h : ℕ)
    (hh : h = ∑ i, tn i + tz + ∑ j, tp j) (α β : ℕ) (hα : 1 ≤ α) (hα2 : α + 2 ≤ h)
    (hβ : β + 2 ≤ h) (hαβ : α + β ≤ h) :
    (n + p + 1 = 3 → α + β = h → tz = 1 →
      ((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
        yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β)) ∧
    (n + p + 1 = 3 → α + β = h → 2 ≤ tz →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-1 : ℤ) 1)) ∧
    (n + p + 1 = 3 → α + β + 1 ≤ h →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-1 : ℤ) 1)) ∧
    (n + p + 1 = 4 → α + β = h → tz = 1 → tp ⟨0, by omega⟩ = 1 →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ x y : ℤ, 0 < x ∧ x < y ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = {x - y, 0, x, y})) ∧
    (n + p + 1 = 4 → α + β = h → 2 ≤ tz ∨ 2 ≤ tp ⟨0, by omega⟩ →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-1 : ℤ) 2)) ∧
    (n + p + 1 = 4 → α + β + 1 ≤ h →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-1 : ℤ) 2)) ∧
    (5 ≤ n + p + 1 →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-(n : ℤ)) p))

end

end MetaMathlibExt
