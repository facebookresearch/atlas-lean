/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.InputOutput.LeontiefNeumann
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

@[expose] public section

namespace MathlibExtTest.Economics.InputOutput.LeontiefNeumann

open MathlibExt.Economics.InputOutput

theorem leontief_inv_two_by_two :
    (1 - !![(1/2 : ℝ), 1/4; 0, 1/2])⁻¹ = !![(2 : ℝ), 1; 0, 2] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply] <;>
    norm_num

theorem leontief_inv_entry_nonneg :
    0 ≤ (1 - !![(1/2 : ℝ), 1/4; 0, 1/2])⁻¹ 0 1 := by
  have hA0 : ∀ i j : Fin 2, 0 ≤ (!![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hrow : ∀ i : Fin 2, ∑ j, (!![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) i j < 1 := by
    intro i
    fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num
  exact inv_one_sub_nonneg_of_rowSum_lt_one hA0 hrow 0 1

theorem leontief_hasSum_two_by_two :
    HasSum (fun n : ℕ => (!![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) ^ n)
      !![(2 : ℝ), 1; 0, 2] := by
  have hA0 : ∀ i j : Fin 2, 0 ≤ (!![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hrow : ∀ i : Fin 2, ∑ j, (!![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) i j < 1 := by
    intro i
    fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num
  have h := hasSum_pow_of_rowSum_lt_one hA0 hrow
  have hinv : (1 - (!![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ =
      !![(2 : ℝ), 1; 0, 2] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply] <;>
      norm_num
  rw [hinv] at h
  exact h

theorem leontief_boundary_not_isUnit :
    ¬ IsUnit ((1 : Matrix (Fin 1) (Fin 1) ℝ) - !![(1 : ℝ)]) := by
  have h0 : (1 : Matrix (Fin 1) (Fin 1) ℝ) - !![(1 : ℝ)] = 0 := by
    ext i j
    fin_cases i; fin_cases j; simp
  rw [h0]
  rintro ⟨u, hu⟩
  have h1 : (0 : Matrix (Fin 1) (Fin 1) ℝ) * (u⁻¹ : (Matrix (Fin 1) (Fin 1) ℝ)ˣ) = 1 := by
    rw [← hu]
    exact u.mul_inv
  rw [zero_mul] at h1
  have h10 := congrFun (congrFun h1 0) 0
  simp at h10

theorem leontief_isUnit_two_by_two :
    IsUnit (1 - !![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hA0 : ∀ i j : Fin 2, 0 ≤ (!![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hrow : ∀ i : Fin 2, ∑ j, (!![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) i j < 1 := by
    intro i
    fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num
  exact isUnit_one_sub_of_rowSum_lt_one hA0 hrow

theorem leontief_det_ne_zero_two_by_two :
    (1 - !![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
  have h : IsUnit (1 - !![(1/2 : ℝ), 1/4; 0, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) :=
    leontief_isUnit_two_by_two
  exact ((Matrix.isUnit_iff_isUnit_det _).mp h).ne_zero

end MathlibExtTest.Economics.InputOutput.LeontiefNeumann