/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.MarshallianDemand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Economics MathlibExt.Economics.Consumer
open MathlibExt.Economics.SecondWelfareTheorem (consumptionSet)

namespace MathlibExtTest.Economics.Consumer.MarshallianDemand

namespace BudgetExamples

/-- Linear utility `x₀ + x₁` on two goods. -/
def linU (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

theorem linU_exists_demand :
    ∃ x, IsMarshallianDemand linU (consumptionSet (Fin 2)) ![1, 2] 2 x := by
  refine exists_isMarshallianDemand ?_ ?_ ?_
  · intro l
    fin_cases l <;> simp
  · refine ⟨0, ?_, ?_⟩
    · show ∀ l, 0 ≤ (0 : Fin 2 → ℝ) l
      intro l
      simp
    · rw [dotProduct_zero]
      norm_num
  · show ContinuousOn (fun x : Fin 2 → ℝ => x 0 + x 1)
      (budgetSet (consumptionSet (Fin 2)) ![1, 2] 2)
    exact ((continuous_apply 0).add (continuous_apply 1)).continuousOn

theorem linU_isMarshallianDemand :
    IsMarshallianDemand linU (consumptionSet (Fin 2)) ![1, 2] 2 ![2, 0] := by
  constructor
  · constructor
    · show ∀ i, 0 ≤ ((![2, 0] : Fin 2 → ℝ) i)
      intro i
      fin_cases i <;> simp
    · simp [dotProduct, Fin.sum_univ_two]
  · intro y hy
    obtain ⟨hymem, hcost⟩ := hy
    have hym : ∀ i, 0 ≤ y i := hymem
    have h1 : (0 : ℝ) ≤ y 1 := hym 1
    simp [linU, dotProduct, Fin.sum_univ_two] at hcost ⊢
    linarith

/-- With zero wealth and positive prices the only affordable bundle is `0`. -/
theorem budgetSet_zero_wealth : budgetSet (consumptionSet (Fin 2)) ![1, 2] 0 = {0} := by
  ext x
  constructor
  · rintro ⟨hmem, hcost⟩
    have hmn : ∀ i, 0 ≤ x i := hmem
    have h0 : (0 : ℝ) ≤ x 0 := hmn 0
    have h1 : (0 : ℝ) ≤ x 1 := hmn 1
    simp [dotProduct, Fin.sum_univ_two] at hcost
    have e0 : x 0 = 0 := by linarith
    have e1 : x 1 = 0 := by linarith
    rw [Set.mem_singleton_iff]
    funext i
    fin_cases i
    · simpa using e0
    · simpa using e1
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨?_, by simp⟩
    show ∀ l, 0 ≤ (0 : Fin 2 → ℝ) l
    intro l
    simp

/-- Negative wealth: the budget set is empty, so no bundle is demanded. -/
theorem no_demand_negative_wealth :
    ¬ ∃ x, IsMarshallianDemand linU (consumptionSet (Fin 2)) ![1, 2] (-1) x := by
  rintro ⟨x, ⟨hmem, hcost⟩, -⟩
  have hmn : ∀ i, 0 ≤ x i := hmem
  have h0 : (0 : ℝ) ≤ x 0 := hmn 0
  have h1 : (0 : ℝ) ≤ x 1 := hmn 1
  simp [dotProduct, Fin.sum_univ_two] at hcost
  linarith

/-- A zero price: good `0` is free and wanted without bound, so no bundle is demanded. -/
theorem no_demand_zero_price :
    ¬ ∃ x, IsMarshallianDemand (fun x : Fin 2 → ℝ => x 0) (consumptionSet (Fin 2)) ![0, 1] 1 x := by
  rintro ⟨x, ⟨hmem, hcost⟩, hmax⟩
  have hmn : ∀ i, 0 ≤ x i := hmem
  have h0 : (0 : ℝ) ≤ x 0 := hmn 0
  have h1 : (0 : ℝ) ≤ x 1 := hmn 1
  simp [dotProduct, Fin.sum_univ_two] at hcost
  have hy : ![x 0 + 1, x 1] ∈ budgetSet (consumptionSet (Fin 2)) (![0, 1] : Fin 2 → ℝ) 1 := by
    constructor
    · show ∀ i, 0 ≤ ((![x 0 + 1, x 1] : Fin 2 → ℝ) i)
      intro i
      fin_cases i <;> simp <;> linarith
    · simp [dotProduct, Fin.sum_univ_two]
      linarith
  have hle := hmax _ hy
  simp only [Matrix.cons_val_zero] at hle
  linarith

end BudgetExamples

end MathlibExtTest.Economics.Consumer.MarshallianDemand
