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

open Economics.Consumer

namespace MathlibExtTest.Economics.Consumer.DemandHomogeneity

/-- The nonnegative orthant in the two-good examples. -/
def orthant : Set (Fin 2 → ℝ) := {x | 0 ≤ x}

/-- Linear utility `x₀ + x₁` on two goods. -/
def linU (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

/-- Tripling prices and wealth preserves the demanded bundles. -/
theorem linU_demand_triple (x : Fin 2 → ℝ) :
    IsMarshallianDemand linU orthant ![3, 6] 6 x ↔
      IsMarshallianDemand linU orthant ![1, 2] 2 x := by
  have hvec : (![3, 6] : Fin 2 → ℝ) = (3 : ℝ) • ![1, 2] := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]; norm_num
  have h6 : (6 : ℝ) = 3 * 2 := by norm_num
  rw [hvec, h6]
  exact isMarshallianDemand_smul_iff linU orthant (by norm_num) _ _ _

/-- The equivalence relates nonempty demand sets: `(2, 0)` is demanded at both prices. -/
theorem linU_demand_witness :
    IsMarshallianDemand linU orthant ![1, 2] 2 ![2, 0] ∧
      IsMarshallianDemand linU orthant ![3, 6] 6 ![2, 0] := by
  have hmem : (![2, 0] : Fin 2 → ℝ) ∈ budgetSet orthant ![1, 2] 2 := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · norm_num [dotProduct, Fin.sum_univ_two]
  have hopt : ∀ y ∈ budgetSet orthant ![1, 2] 2, linU y ≤ linU ![2, 0] := by
    intro y hy
    have hle : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ y ≤ 2 := hy.2
    have hcost : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + 2 * y 1 := by
      simp [dotProduct, Fin.sum_univ_two]
    have hy1 : 0 ≤ y 1 := hy.1 1
    have hwit : linU (![2, 0] : Fin 2 → ℝ) = 2 := by simp [linU]
    have hlin : linU y = y 0 + y 1 := rfl
    rw [hlin, hwit]
    rw [hcost] at hle
    linarith
  have h1 : IsMarshallianDemand linU orthant ![1, 2] 2 ![2, 0] := ⟨hmem, hopt⟩
  exact ⟨h1, (linU_demand_triple ![2, 0]).mpr h1⟩

/-- Zero scaling breaks the identity: every nonnegative bundle becomes affordable. -/
theorem budgetSet_zero_smul_ne :
    budgetSet orthant ((0 : ℝ) • ![1, 2]) (0 * 2) ≠ budgetSet orthant ![1, 2] 2 := by
  intro h
  have hmem : (![3, 0] : Fin 2 → ℝ) ∈ budgetSet orthant ((0 : ℝ) • ![1, 2]) (0 * 2) := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · rw [smul_dotProduct, smul_eq_mul, zero_mul]
      norm_num
  have hnot : (![3, 0] : Fin 2 → ℝ) ∉ budgetSet orthant ![1, 2] 2 := by
    intro hcon
    have hle : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![3, 0] ≤ 2 := hcon.2
    norm_num [dotProduct, Fin.sum_univ_two] at hle
  rw [h] at hmem
  exact hnot hmem

/-- Negative scaling reverses the budget inequality. -/
theorem budgetSet_neg_smul_ne :
    budgetSet orthant ((-1 : ℝ) • ![1, 2]) (-1 * 2) ≠ budgetSet orthant ![1, 2] 2 := by
  intro h
  have hmem : (![0, 0] : Fin 2 → ℝ) ∈ budgetSet orthant ![1, 2] 2 := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · norm_num [dotProduct, Fin.sum_univ_two]
  have hnot : (![0, 0] : Fin 2 → ℝ) ∉ budgetSet orthant ((-1 : ℝ) • ![1, 2]) (-1 * 2) := by
    intro hcon
    have hle := hcon.2
    norm_num [dotProduct, Fin.sum_univ_two] at hle
  rw [← h] at hmem
  exact hnot hmem

/-- The shared API covers consumption sets outside the nonnegative orthant. -/
example : IsMarshallianDemand (fun _ => 0)
    ({![-1, 0]} : Set (Fin 2 → ℝ)) ((3 : ℝ) • ![1, 2]) (3 * 2) ![-1, 0] := by
  apply (isMarshallianDemand_smul_iff
    (fun _ => 0) {![-1, 0]} (by norm_num : (0 : ℝ) < 3) ![1, 2] 2 ![-1, 0]).mpr
  refine ⟨⟨by simp, ?_⟩, fun _ _ => le_rfl⟩
  norm_num [dotProduct, Fin.sum_univ_two]

/-- Positive scaling preserves any fixed consumption set, including the empty set. -/
example (X : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) (w : ℝ) :
    budgetSet X ((2 : ℝ) • p) (2 * w) = budgetSet X p w :=
  budgetSet_smul X (by norm_num) p w

end MathlibExtTest.Economics.Consumer.DemandHomogeneity
