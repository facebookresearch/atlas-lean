/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.ConstantReturns
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Ineq

@[expose] public section

/-! Tests for `MathlibExt.Economics.Producer.ConstantReturns`: concrete instances with exact values. -/

namespace MathlibExtTest.Economics.Producer.ConstantReturns

open _root_.Economics.Producer

section Test

/-- The ray through `![1, -1]` has constant returns. -/
theorem test_ray_hasConstantReturns :
    HasConstantReturns (Y := {y : Fin 2 → ℝ | ∃ t : ℝ, 0 ≤ t ∧ y = t • ![1, -1]}) := by
  intro y hy s hs
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨s * t, mul_nonneg hs ht, smul_smul s t _⟩

/-- `![1, 1] ⬝ᵥ ![1, -1] = 0`: the generator earns zero at these prices. -/
theorem test_dotProduct_generator :
    ![1, 1] ⬝ᵥ ![1, -1] = (0 : ℝ) := by
  simp [dotProduct, Fin.sum_univ_two]

/-- At prices `![1, 1]`, inaction maximizes profit over the ray. -/
theorem test_zero_isProfitMax :
    IsProfitMax {y : Fin 2 → ℝ | ∃ t : ℝ, 0 ≤ t ∧ y = t • ![1, -1]} ![1, 1] 0 := by
  constructor
  · exact ⟨0, le_rfl, by simp⟩
  · intro y' hy'
    obtain ⟨t, ht, rfl⟩ := hy'
    rw [dotProduct_smul, dotProduct_zero, test_dotProduct_generator, smul_zero]

/-- The main theorem gives zero profit at the maximizer. -/
theorem test_zero_profit :
    ![1, 1] ⬝ᵥ (0 : Fin 2 → ℝ) = 0 :=
  IsProfitMax.dotProduct_eq_zero_of_hasConstantReturns
    test_ray_hasConstantReturns test_zero_isProfitMax

/-- Every feasible plan earns at most zero. -/
theorem test_nonpos :
    ∀ z ∈ {y : Fin 2 → ℝ | ∃ t : ℝ, 0 ≤ t ∧ y = t • ![1, -1]},
      ![1, 1] ⬝ᵥ z ≤ 0 :=
  IsProfitMax.dotProduct_nonpos_of_hasConstantReturns
    test_ray_hasConstantReturns test_zero_isProfitMax

/-- The generator `![1, -1]` earns `0 ≤ 0`. -/
theorem test_generator_nonpos : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, -1] ≤ 0 :=
  test_nonpos ![1, -1] ⟨1, zero_le_one, by simp⟩

end Test

end MathlibExtTest.Economics.Producer.ConstantReturns
