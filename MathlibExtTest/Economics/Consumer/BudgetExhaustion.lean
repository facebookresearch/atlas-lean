/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.BudgetExhaustion
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Economics MathlibExt.Economics.Consumer
open MathlibExt.Economics.SecondWelfareTheorem (consumptionSet)

namespace MathlibExtTest.Economics.Consumer.BudgetExhaustion

namespace BudgetExhaustionExamples

/-- Linear utility `x₀ + x₁` on two goods. -/
def linU (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

theorem linU_locallyNonsatiated : SecondWelfareTheorem.LocallyNonsatiated linU := by
  intro z hz ε hε
  refine ⟨fun l => z l + ε / 2, fun l => by have h := hz l; linarith, ?_, ?_⟩
  · rw [dist_pi_lt_iff hε]
    intro b
    rw [Real.dist_eq]
    have h2 : (z b + ε / 2) - z b = ε / 2 := by ring
    rw [h2, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
    linarith
  · unfold linU
    linarith

theorem linU_demand_exhausts (x : Fin 2 → ℝ)
    (hx : x ∈ marshallianDemand linU ![1, 2] 2) :
    (![1, 2] : Fin 2 → ℝ) ⬝ᵥ x = 2 := by
  exact dotProduct_eq_of_isMarshallianDemand linU_locallyNonsatiated hx

/-- A satiated utility with bliss point `(1, 1)`. -/
def blissU (x : Fin 2 → ℝ) : ℝ := -((x 0 - 1) ^ 2 + (x 1 - 1) ^ 2)

/-- The bliss point is demanded at prices `(1, 1)` and wealth `4`. -/
theorem blissU_isMarshallianDemand :
    ![1, 1] ∈ marshallianDemand blissU ![1, 1] 4 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro l
    fin_cases l <;> norm_num
  · simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one]
    norm_num
  · intro y hy
    unfold blissU
    have h0 : (0:ℝ) ≤ (y 0 - 1) ^ 2 := sq_nonneg _
    have h1 : (0:ℝ) ≤ (y 1 - 1) ^ 2 := sq_nonneg _
    norm_num
    linarith

/-- ... but it leaves wealth unspent: without local nonsatiation the budget need not bind. -/
theorem blissU_not_exhausted : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] ≠ 4 := by
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one]
  norm_num

theorem blissU_not_locallyNonsatiated : ¬ SecondWelfareTheorem.LocallyNonsatiated blissU := by
  intro h
  have hmem : (![1, 1] : Fin 2 → ℝ) ∈ SecondWelfareTheorem.consumptionSet (Fin 2) := by
    intro l
    fin_cases l <;> norm_num
  obtain ⟨z, hzmem, hdist, hgt⟩ := h _ hmem 1 one_pos
  unfold blissU at hgt
  have h0 : (0:ℝ) ≤ (z 0 - 1) ^ 2 := sq_nonneg _
  have h1 : (0:ℝ) ≤ (z 1 - 1) ^ 2 := sq_nonneg _
  norm_num at hgt
  linarith

end BudgetExhaustionExamples

end MathlibExtTest.Economics.Consumer.BudgetExhaustion
