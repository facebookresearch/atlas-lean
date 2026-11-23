/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.ProbabilityRanking
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for the probability ranking principle
-/

set_option autoImplicit false

open Cslib.InformationRetrieval

namespace CSLibExtTest.InformationRetrieval.ProbabilityRanking

/-- The zero law has zero marginals. -/
example {N : ℕ} (i : Fin N) : relevanceMarginal (fun _ => 0) i = 0 := by
  simp [relevanceMarginal]

/-- The zero law has zero expected precision. -/
example {N k : ℕ} (r : Fin k → Fin N) :
    expectedPrecisionAt (fun _ => 0) r = 0 := by
  simp [expectedPrecisionAt]

/-- Expected precision at the empty cutoff is zero for every joint law. -/
example {N : ℕ} (μ : (Fin N → Bool) → ℝ) (r : Fin 0 → Fin N) :
    expectedPrecisionAt μ r = 0 := by
  simp [expectedPrecisionAt, precisionAt]

/-- The marginal-average identity, as an example. -/
example {N k : ℕ} (μ : (Fin N → Bool) → ℝ) (r : Fin k → Fin N) (hk : k ≠ 0) :
    expectedPrecisionAt μ r =
      (∑ j, relevanceMarginal μ (r j)) / (k : ℝ) :=
  expectedPrecisionAt_eq_average_marginals μ r hk

/-- At cutoff two, the identity is the average of the two selected marginals. -/
example {N : ℕ} (μ : (Fin N → Bool) → ℝ) (a b : Fin N) :
    expectedPrecisionAt μ ![a, b] =
      (relevanceMarginal μ a + relevanceMarginal μ b) / 2 := by
  rw [expectedPrecisionAt_eq_average_marginals μ ![a, b] (by norm_num),
    Fin.sum_univ_two]
  norm_num

/-- An optimal marginal-sorted prefix exists for any real weights, as an
example. -/
example {N k : ℕ} (hk : k ≤ N) (μ : (Fin N → Bool) → ℝ) :
    ∃ s : {s : Equiv.Perm (Fin N) // Antitone (relevanceMarginal μ ∘ s)},
      ∀ r : Fin k → Fin N, Function.Injective r →
        expectedPrecisionAt μ r ≤
          expectedPrecisionAt μ (fun i => s.1 (Fin.castLE hk i)) :=
  exists_sorted_expectedPrecisionAt hk μ

/-! ### A point-mass law on two documents

With probability one, document `0` is relevant and document `1` is not. -/

/-- The point-mass law at the relevance vector in which only document `0` is relevant. -/
noncomputable def pointLaw : (Fin 2 → Bool) → ℝ :=
  fun rel => if rel = ![true, false] then 1 else 0

/-- Every relevance vector other than `![true, false]` has weight `0`. -/
theorem pointLaw_of_ne {rel : Fin 2 → Bool} (h : rel ≠ ![true, false]) : pointLaw rel = 0 := by
  simp [pointLaw, h]

/-- Document `0` has marginal relevance `1` under `pointLaw`. -/
theorem pointLaw_marginal_zero : relevanceMarginal pointLaw 0 = 1 := by
  rw [relevanceMarginal, Fintype.sum_eq_single ![true, false] fun rel h => by
    rw [pointLaw_of_ne h, zero_mul]]
  simp [pointLaw]

/-- Document `1` has marginal relevance `0` under `pointLaw`. -/
theorem pointLaw_marginal_one : relevanceMarginal pointLaw 1 = 0 := by
  rw [relevanceMarginal, Fintype.sum_eq_single ![true, false] fun rel h => by
    rw [pointLaw_of_ne h, zero_mul]]
  simp [pointLaw]

/-- Ranking the relevant document first has expected precision `1` at cutoff one. -/
example : expectedPrecisionAt pointLaw ![(0 : Fin 2)] = 1 := by
  rw [expectedPrecisionAt, Fintype.sum_eq_single ![true, false] fun rel h => by
    rw [pointLaw_of_ne h, zero_mul]]
  simp [pointLaw, precisionAt]

/-- Ranking the irrelevant document first has expected precision `0` at cutoff one. -/
example : expectedPrecisionAt pointLaw ![(1 : Fin 2)] = 0 := by
  rw [expectedPrecisionAt, Fintype.sum_eq_single ![true, false] fun rel h => by
    rw [pointLaw_of_ne h, zero_mul]]
  simp [pointLaw, precisionAt]

/-- At cutoff two, the ranking `1, 0` has expected precision `1 / 2`. -/
example : expectedPrecisionAt pointLaw ![(1 : Fin 2), 0] = 1 / 2 := by
  have hcard : (Finset.univ.filter fun i : Fin 2 =>
      ![true, false] (![(1 : Fin 2), 0] i) = true).card = 1 := by
    decide
  rw [expectedPrecisionAt, Fintype.sum_eq_single ![true, false] fun rel h => by
    rw [pointLaw_of_ne h, zero_mul]]
  simp [pointLaw, precisionAt, hcard]

/-- The identity ranking is sorted by marginal relevance (`1` then `0`), so by
`expectedPrecisionAt_le_sortedPrefix` its cutoff-one prefix `![0]` bounds the competing prefix
`![1]`. -/
example : expectedPrecisionAt pointLaw ![(1 : Fin 2)] ≤
    expectedPrecisionAt pointLaw ![(0 : Fin 2)] := by
  have hsorted : Antitone (relevanceMarginal pointLaw ∘ ⇑(Equiv.refl (Fin 2))) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [pointLaw_marginal_zero, pointLaw_marginal_one] at hij ⊢
  have h := expectedPrecisionAt_le_sortedPrefix (N := 2) (k := 1) (by norm_num)
    (r := ![(1 : Fin 2)]) (Function.injective_of_subsingleton _) ⟨Equiv.refl _, hsorted⟩
  convert h using 2
  funext i
  fin_cases i
  rfl

end CSLibExtTest.InformationRetrieval.ProbabilityRanking
