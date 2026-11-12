/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.DemandHomogeneity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Economics MathlibExt.Economics.Consumer

namespace MathlibExtTest.Economics.Consumer.DemandHomogeneity

namespace HomogeneityExamples

/-- Linear utility `x₀ + x₁` on two goods. -/
def linU (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

/-- Tripling prices and wealth: demand at `((3, 6), 6)` equals demand at `((1, 2), 2)`. -/
theorem linU_demand_triple (x : Fin 2 → ℝ) :
    x ∈ marshallianDemand linU ![3, 6] 6 ↔ x ∈ marshallianDemand linU ![1, 2] 2 := by
  have hvec : (![3, 6] : Fin 2 → ℝ) = (3 : ℝ) • ![1, 2] := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]; norm_num
  have h6 : (6 : ℝ) = 3 * 2 := by norm_num
  rw [hvec, h6]
  exact isMarshallianDemand_smul_iff linU (by norm_num) _ _ _

/-- The bundle `(2, 0)` is demanded both at `((1, 2), 2)` and at the tripled `((3, 6), 6)`, so the
equivalence above relates nonempty demand sets. -/
theorem linU_demand_witness :
    ![2, 0] ∈ marshallianDemand linU ![1, 2] 2 ∧
      ![2, 0] ∈ marshallianDemand linU ![3, 6] 6 := by
  have hmem : (![2, 0] : Fin 2 → ℝ) ∈ budgetSet ![1, 2] 2 := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · have hcost : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![2, 0] = 2 := by
        simp [dotProduct, Fin.sum_univ_two]
      rw [hcost]
  have hopt : ∀ y ∈ budgetSet ![1, 2] 2, linU y ≤ linU ![2, 0] := by
    intro y hy
    have hle : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ y ≤ 2 := hy.2
    have hcost : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + 2 * y 1 := by
      simp [dotProduct, Fin.sum_univ_two]
    have hy1 : 0 ≤ y 1 := Pi.le_def.mp hy.1 1
    have hwit : linU (![2, 0] : Fin 2 → ℝ) = 2 := by
      simp [linU]
    have hlin : linU y = y 0 + y 1 := rfl
    rw [hlin, hwit]
    rw [hcost] at hle
    linarith
  have h1 : ![2, 0] ∈ marshallianDemand linU ![1, 2] 2 := ⟨hmem, hopt⟩
  have hvec : (![3, 6] : Fin 2 → ℝ) = (3 : ℝ) • ![1, 2] := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]; norm_num
  have h6 : (6 : ℝ) = 3 * 2 := by norm_num
  have h2 : ![2, 0] ∈ marshallianDemand linU ![3, 6] 6 := by
    rw [hvec, h6]
    exact (isMarshallianDemand_smul_iff linU (by norm_num : (0 : ℝ) < 3) ![1, 2] 2
      ![2, 0]).mpr h1
  exact ⟨h1, h2⟩

/-- Zero scaling breaks the identity: at zero prices and wealth every bundle is affordable. -/
theorem budgetSet_zero_smul_ne :
    budgetSet ((0 : ℝ) • ![1, 2]) (0 * 2) ≠ budgetSet ![1, 2] 2 := by
  intro h
  have hmem : (![3, 0] : Fin 2 → ℝ) ∈ budgetSet ((0 : ℝ) • ![1, 2]) (0 * 2) := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · rw [smul_dotProduct, smul_eq_mul, zero_mul]
      norm_num
  have hnot : (![3, 0] : Fin 2 → ℝ) ∉ budgetSet ![1, 2] 2 := by
    intro hcon
    have hle : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![3, 0] ≤ 2 := hcon.2
    have hcost : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![3, 0] = 3 := by
      simp [dotProduct, Fin.sum_univ_two]
    rw [hcost] at hle
    norm_num at hle
  rw [h] at hmem
  exact hnot hmem

/-- Negative scaling breaks the identity: it reverses the budget inequality. -/
theorem budgetSet_neg_smul_ne :
    budgetSet ((-1 : ℝ) • ![1, 2]) (-1 * 2) ≠ budgetSet ![1, 2] 2 := by
  intro h
  have hmem : (![0, 0] : Fin 2 → ℝ) ∈ budgetSet ![1, 2] 2 := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · have hcost : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![0, 0] = 0 := by
        simp [dotProduct, Fin.sum_univ_two]
      rw [hcost]
      norm_num
  have hnot : (![0, 0] : Fin 2 → ℝ) ∉ budgetSet ((-1 : ℝ) • ![1, 2]) (-1 * 2) := by
    intro hcon
    have hle : (((-1 : ℝ) • (![1, 2] : Fin 2 → ℝ)) ⬝ᵥ (![0, 0] : Fin 2 → ℝ)) ≤ -1 * 2 :=
      hcon.2
    have hcost : (((-1 : ℝ) • (![1, 2] : Fin 2 → ℝ)) ⬝ᵥ (![0, 0] : Fin 2 → ℝ)) = 0 := by
      rw [smul_dotProduct, smul_eq_mul]
      have h0 : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![0, 0] = 0 := by
        simp [dotProduct, Fin.sum_univ_two]
      rw [h0, mul_zero]
    rw [hcost] at hle
    norm_num at hle
  rw [← h] at hmem
  exact hnot hmem

end HomogeneityExamples

end MathlibExtTest.Economics.Consumer.DemandHomogeneity
