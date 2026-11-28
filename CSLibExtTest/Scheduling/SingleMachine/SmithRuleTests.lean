/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.SingleMachine.SmithRule
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Smith's rule checks

Concrete consumers of `CSLibExt.Scheduling.SingleMachine.SmithRule`: a three-job instance with a
zero weight, where the order of Smith's rule beats an order that violates it; two jobs with equal
ratios, where both orders follow the rule and tie; a zero-weight, zero-length job placed first,
which breaks the rule's zero-weights-last clause but not the cross-product condition; the special
case `w = 1`, shortest processing time first, over `ℕ`; and the empty job type. Elaboration
checks, not results.
-/

namespace CSLibExtTest.Scheduling.SingleMachine.SmithRule

open Cslib.Scheduling.SingleMachine

/-! ### Three jobs, one of weight zero -/

/-- Processing times `2, 1, 3`. -/
noncomputable def p : Fin 3 → ℝ := ![2, 1, 3]

/-- Weights `1, 3, 0`: job `2` has weight zero and goes last. -/
noncomputable def w : Fin 3 → ℝ := ![1, 3, 0]

theorem p_nonneg : ∀ j, 0 ≤ p j := by
  intro j; fin_cases j <;> norm_num [p]

theorem w_nonneg : ∀ j, 0 ≤ w j := by
  intro j; fin_cases j <;> norm_num [w]

-- `[1, 0, 2]` follows Smith's rule: `1 / 3 < 2 / 1`, and the weight-zero job is last.
theorem smith_order :
    [(1 : Fin 3), 0, 2].Pairwise fun i j => (0 < w j → 0 < w i) ∧ p i * w j ≤ p j * w i := by
  simp [p, w]
  norm_num

theorem isSchedule_smith : IsSchedule [(1 : Fin 3), 0, 2] := ⟨by decide, by decide⟩

theorem smith_optimal (τ : List (Fin 3)) (hτ : IsSchedule τ) :
    totalWeightedCompletionTime p w [1, 0, 2] ≤ totalWeightedCompletionTime p w τ :=
  (smithRule_minimizes_totalWeightedCompletionTime p_nonneg w_nonneg).2 _ τ isSchedule_smith hτ
    smith_order

-- Its value is `3 * 1 + 1 * 3 + 0 * 6 = 6`.
example : totalWeightedCompletionTime p w [1, 0, 2] = 6 := by
  simp [totalWeightedCompletionTime, Fin.sum_univ_three, completionTime, p, w]
  norm_num

-- `[0, 1, 2]` violates the rule (`2 * 3 > 1 * 1`) and costs `1 * 2 + 3 * 3 = 11`.
example :
    ¬ [(0 : Fin 3), 1, 2].Pairwise fun i j => (0 < w j → 0 < w i) ∧ p i * w j ≤ p j * w i := by
  simp [p, w]
  norm_num

example : totalWeightedCompletionTime p w [0, 1, 2] = 11 := by
  simp [totalWeightedCompletionTime, Fin.sum_univ_three, completionTime, p, w]
  norm_num

-- Putting the weight-zero job first is not Smith's rule.
example :
    ¬ [(2 : Fin 3), 1, 0].Pairwise fun i j => (0 < w j → 0 < w i) ∧ p i * w j ≤ p j * w i := by
  simp [p, w]

/-! ### Equal ratios: both orders follow the rule and tie -/

/-- Processing times `1, 2`. -/
noncomputable def p₂ : Fin 2 → ℝ := ![1, 2]

/-- Weights `1, 2`, so both jobs have ratio `1`. -/
noncomputable def w₂ : Fin 2 → ℝ := ![1, 2]

example : totalWeightedCompletionTime p₂ w₂ [0, 1] = totalWeightedCompletionTime p₂ w₂ [1, 0] := by
  have hp : ∀ j, 0 ≤ p₂ j := by intro j; fin_cases j <;> norm_num [p₂]
  have hw : ∀ j, 0 ≤ w₂ j := by intro j; fin_cases j <;> norm_num [w₂]
  have h01 : [(0 : Fin 2), 1].Pairwise fun i j =>
      (0 < w₂ j → 0 < w₂ i) ∧ p₂ i * w₂ j ≤ p₂ j * w₂ i := by
    simp [p₂, w₂]
  have h10 : [(1 : Fin 2), 0].Pairwise fun i j =>
      (0 < w₂ j → 0 < w₂ i) ∧ p₂ i * w₂ j ≤ p₂ j * w₂ i := by
    simp [p₂, w₂]
  have hs01 : IsSchedule [(0 : Fin 2), 1] := ⟨by decide, by decide⟩
  have hs10 : IsSchedule [(1 : Fin 2), 0] := ⟨by decide, by decide⟩
  have h := (smithRule_minimizes_totalWeightedCompletionTime hp hw).2
  exact le_antisymm (h _ _ hs01 hs10 h01) (h _ _ hs10 hs01 h10)

/-! ### A zero-weight, zero-length job first -/

/-- Job `0` has length zero and weight zero; job `1` has length and weight one. -/
noncomputable def p₃ : Fin 2 → ℝ := ![0, 1]

/-- Weights `0, 1`. -/
noncomputable def w₃ : Fin 2 → ℝ := ![0, 1]

-- `[0, 1]` puts the zero-weight job first, against the rule, yet it satisfies the cross-product
-- condition and so is still optimal.
example :
    ¬ [(0 : Fin 2), 1].Pairwise fun i j => (0 < w₃ j → 0 < w₃ i) ∧ p₃ i * w₃ j ≤ p₃ j * w₃ i := by
  simp [p₃, w₃]

example (τ : List (Fin 2)) (hτ : IsSchedule τ) :
    totalWeightedCompletionTime p₃ w₃ [0, 1] ≤ totalWeightedCompletionTime p₃ w₃ τ :=
  totalWeightedCompletionTime_le_of_pairwise ⟨by decide, by decide⟩ hτ (by simp [p₃, w₃])

/-! ### Unit weights over `ℕ`: shortest processing time first -/

/-- Processing times `3, 1, 2` in `ℕ`. -/
def pNat : Fin 3 → ℕ := ![3, 1, 2]

example (τ : List (Fin 3)) (hτ : IsSchedule τ) :
    totalWeightedCompletionTime pNat (fun _ => 1) [1, 2, 0] ≤
      totalWeightedCompletionTime pNat (fun _ => 1) τ :=
  totalWeightedCompletionTime_le_of_pairwise ⟨by decide, by decide⟩ hτ (by decide)

/-! ### No jobs -/

example (p w : Empty → ℝ) :
    ∃ σ, IsSchedule σ ∧ σ.Pairwise fun i j => (0 < w j → 0 < w i) ∧ p i * w j ≤ p j * w i :=
  (smithRule_minimizes_totalWeightedCompletionTime (fun j => j.elim) (fun j => j.elim)).1

end CSLibExtTest.Scheduling.SingleMachine.SmithRule
