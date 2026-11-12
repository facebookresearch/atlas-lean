/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.MarshallianDemand
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Economics.Consumer

namespace MathlibExtTest.Economics.Consumer.MarshallianDemand

namespace BudgetExamples

/-- Linear utility `x₀ + x₁` on two goods. -/
def linU (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

theorem linU_demand_nonempty : (marshallianDemand linU ![1, 2] 2).Nonempty := by
  refine marshallianDemand_nonempty ?_ ?_ ?_
  · intro l
    fin_cases l <;> simp
  · exact ⟨0, le_rfl, by rw [dotProduct_zero]; norm_num⟩
  · show ContinuousOn (fun x : Fin 2 → ℝ => x 0 + x 1) (budgetSet ![1, 2] 2)
    exact ((continuous_apply 0).add (continuous_apply 1)).continuousOn

theorem linU_mem_demand : ![2, 0] ∈ marshallianDemand linU ![1, 2] 2 := by
  constructor
  · constructor
    · intro i
      fin_cases i <;> simp
    · simp [dotProduct, Fin.sum_univ_two]
  · intro y hy
    obtain ⟨hyle, hcost⟩ := hy
    have h1 : (0 : ℝ) ≤ y 1 := hyle 1
    simp [linU, dotProduct, Fin.sum_univ_two] at hcost ⊢
    linarith

/-- With zero wealth and positive prices the only affordable bundle is `0`. -/
theorem budgetSet_zero_wealth : budgetSet (![1, 2] : Fin 2 → ℝ) 0 = {0} := by
  ext x
  constructor
  · rintro ⟨hyle, hcost⟩
    have h0 : (0 : ℝ) ≤ x 0 := hyle 0
    have h1 : (0 : ℝ) ≤ x 1 := hyle 1
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
    refine ⟨le_rfl, by simp⟩

/-- Negative wealth: the budget set is empty, and so is demand. -/
theorem demand_negative_wealth : marshallianDemand linU ![1, 2] (-1) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro x ⟨⟨hyle, hcost⟩, -⟩
  have h0 : (0 : ℝ) ≤ x 0 := hyle 0
  have h1 : (0 : ℝ) ≤ x 1 := hyle 1
  simp [dotProduct, Fin.sum_univ_two] at hcost
  linarith

/-- A zero price: good `0` is free and wanted without bound, so demand is empty. -/
theorem demand_zero_price :
    marshallianDemand (fun x : Fin 2 → ℝ => x 0) ![0, 1] 1 = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro x ⟨⟨hyle, hcost⟩, hmax⟩
  have h0 : (0 : ℝ) ≤ x 0 := hyle 0
  have h1 : (0 : ℝ) ≤ x 1 := hyle 1
  simp [dotProduct, Fin.sum_univ_two] at hcost
  have hy : ![x 0 + 1, x 1] ∈ budgetSet (![0, 1] : Fin 2 → ℝ) 1 := by
    constructor
    · intro i
      fin_cases i <;> simp <;> linarith
    · simp [dotProduct, Fin.sum_univ_two]
      linarith
  have hle := hmax _ hy
  simp only [Matrix.cons_val_zero] at hle
  linarith

end BudgetExamples

end MathlibExtTest.Economics.Consumer.MarshallianDemand
