/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RegularOverpartitionDensityExistsGamma0LowerUnipotentTZpowDecomposition
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.Combinatorics.Enumerative.RegularOverpartitionDensityExistsGamma0LowerUnipotentTZpowDecomposition

open scoped MatrixGroups

private def AtestTwo : SL(2, ℤ) := ⟨!![1, 0; -2, 1], by simp [Matrix.det_fin_two]⟩

private def AtestFour : SL(2, ℤ) := ⟨!![1, 0; -4, 1], by simp [Matrix.det_fin_two]⟩

/-- For `N = 2` and `γ = 1`, the unique divisor is `2`. -/
theorem unique_delta_for_one_at_two (δ : ℕ)
    (hδ : δ ∣ 2 ∧ ∃ A ∈ CongruenceSubgroup.Gamma0 2, ∃ h : ℤ,
      (1 : SL(2, ℤ)) = A * ⟨!![1, 0; (δ : ℤ), 1], by simp [Matrix.det_fin_two]⟩
        * ModularGroup.T ^ h) :
    δ = 2 := by
  have hsq2 : Squarefree (2 : ℕ) := Nat.prime_two.prime.squarefree
  obtain ⟨δ₀, -, huniq⟩ :=
    MetaMathlibExt.exists_gamma0_lowerUnipotent_T_zpow_decomposition 2 (Or.inl hsq2) 1
  have h2 : (2 : ℕ) ∣ 2 ∧ ∃ A ∈ CongruenceSubgroup.Gamma0 2, ∃ h : ℤ,
      (1 : SL(2, ℤ)) = A * ⟨!![1, 0; ((2 : ℕ) : ℤ), 1], by simp [Matrix.det_fin_two]⟩
        * ModularGroup.T ^ h := by
    refine ⟨dvd_rfl, AtestTwo, ?_, 0, ?_⟩
    · have h10 : AtestTwo.1 1 0 = -2 := rfl
      rw [CongruenceSubgroup.Gamma0_mem, h10]
      decide
    · rw [zpow_zero, mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;> decide
  exact (huniq δ hδ).trans (huniq 2 h2).symm

/-- For `N = 4` and `γ = 1`, the unique divisor is `4`. -/
theorem unique_delta_for_one_at_four (δ : ℕ)
    (hδ : δ ∣ 4 ∧ ∃ A ∈ CongruenceSubgroup.Gamma0 4, ∃ h : ℤ,
      (1 : SL(2, ℤ)) = A * ⟨!![1, 0; (δ : ℤ), 1], by simp [Matrix.det_fin_two]⟩
        * ModularGroup.T ^ h) :
    δ = 4 := by
  have h42 : (4 : ℕ) / 2 = 2 := by norm_num
  have hsq4 : 2 ∣ 4 ∧ Squarefree ((4 : ℕ) / 2) := by
    rw [h42]
    exact ⟨by norm_num, Nat.prime_two.prime.squarefree⟩
  obtain ⟨δ₀, -, huniq⟩ :=
    MetaMathlibExt.exists_gamma0_lowerUnipotent_T_zpow_decomposition 4 (Or.inr hsq4) 1
  have h4 : (4 : ℕ) ∣ 4 ∧ ∃ A ∈ CongruenceSubgroup.Gamma0 4, ∃ h : ℤ,
      (1 : SL(2, ℤ)) = A * ⟨!![1, 0; ((4 : ℕ) : ℤ), 1], by simp [Matrix.det_fin_two]⟩
        * ModularGroup.T ^ h := by
    refine ⟨dvd_rfl, AtestFour, ?_, 0, ?_⟩
    · have h10 : AtestFour.1 1 0 = -4 := rfl
      rw [CongruenceSubgroup.Gamma0_mem, h10]
      decide
    · rw [zpow_zero, mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;> decide
  exact (huniq δ hδ).trans (huniq 4 h4).symm

end MathlibExtTest.Combinatorics.Enumerative.RegularOverpartitionDensityExistsGamma0LowerUnipotentTZpowDecomposition
