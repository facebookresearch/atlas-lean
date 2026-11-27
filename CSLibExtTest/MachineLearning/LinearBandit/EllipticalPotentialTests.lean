/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.LinearBandit.EllipticalPotential
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Basic
import MathlibExt.LinearAlgebra.Matrix.PosSemidefDeterminant

/-!
# Elliptical potential lemma tests

Boundary checks for the elliptical potential lemma: zero rounds, one
dimension, a concrete determinant-trace evaluation, and the distinction
between the inverse-matrix quadratic form and the unweighted squared norm.
-/

namespace CSLibExtTest.MachineLearning.LinearBandit

open Cslib.MachineLearning.LinearBandit

/-- T1: zero rounds give the initial matrix and an empty potential sum. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V0 : Matrix ι ι ℝ) (a : ℕ → ι → ℝ) :
    ellipticalGram V0 a 0 = V0 ∧
      ∑ k ∈ Finset.range 0, ellipticalPotential V0 a k = 0 :=
  ⟨ellipticalGram_zero V0 a, by simp⟩

/-- T1: zero actions leave the gram matrix unchanged. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V0 : Matrix ι ι ℝ) (a : ℕ → ι → ℝ) (t : ℕ) (ha0 : ∀ k, a k = 0) :
    ellipticalGram V0 a t = V0 := by
  simp only [ellipticalGram, ha0, Matrix.zero_vecMulVec, Finset.sum_const_zero,
    add_zero]

/-- T2: one dimension with identity initial matrix and constant action one. -/
example : ellipticalPotential (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 0 = 1 ∧
    ellipticalPotential (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 1 = 1 / 2 ∧
    ∑ k ∈ Finset.range 2,
      ellipticalPotential (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) k
      = 3 / 2 := by
  have hG0 : ellipticalGram (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 0 = 1 :=
    ellipticalGram_zero _ _
  have hinv1 : ((1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = 1 :=
    Matrix.inv_eq_right_inv (mul_one _)
  have hq0 : ellipticalQuadratic (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 0
      = 1 := by
    rw [ellipticalQuadratic, hG0, hinv1, Matrix.one_mulVec]
    simp [dotProduct]
  have hG1 : ellipticalGram (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 1
      = (2 : ℝ) • 1 := by
    ext i j; fin_cases i; fin_cases j
    simp [ellipticalGram, Matrix.add_apply, Matrix.vecMulVec_apply,
      Matrix.one_apply_eq, Matrix.smul_apply]
    norm_num
  have hinv : ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = (2⁻¹ : ℝ) • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_assoc, one_mul, ← smul_assoc, smul_eq_mul,
      mul_inv_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num), one_smul]
  have hq1 : ellipticalQuadratic (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 1
      = 1 / 2 := by
    rw [ellipticalQuadratic, hG1, hinv, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul]
    simp [dotProduct, smul_eq_mul]
  have hp0 : ellipticalPotential (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 0
      = 1 := by
    rw [ellipticalPotential, hq0]; norm_num
  have hp1 : ellipticalPotential (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 1
      = 1 / 2 := by
    rw [ellipticalPotential, hq1, min_eq_right (by norm_num : ((1 : ℝ) / 2) ≤ 1)]
  refine ⟨hp0, hp1, ?_⟩
  show ∑ k ∈ Finset.range (1 + 1), ellipticalPotential 1 (fun _ _ => 1) k
    = 3 / 2
  rw [Finset.sum_range_succ, Finset.sum_range_one, hp0, hp1]
  norm_num

/-- T3: determinant-trace check on a concrete two-by-two diagonal matrix. -/
example : (Matrix.diagonal ![2, 3] : Matrix (Fin 2) (Fin 2) ℝ).det = 6 ∧
    (Matrix.diagonal ![2, 3] : Matrix (Fin 2) (Fin 2) ℝ).trace = 5 ∧
    (6 : ℝ) ≤ ((5 : ℝ) / 2) ^ 2 := by
  have hdet2 : (Matrix.diagonal ![2, 3] : Matrix (Fin 2) (Fin 2) ℝ).det = 6 := by
    norm_num [Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  have htr2 : (Matrix.diagonal ![2, 3] : Matrix (Fin 2) (Fin 2) ℝ).trace = 5 := by
    norm_num [Matrix.trace_diagonal, Fin.sum_univ_two, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  have hpsd2 : (Matrix.diagonal ![2, 3] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by
      fin_cases i <;> norm_num [Matrix.cons_val_one, Matrix.cons_val_zero])
  have hd2 : 0 < Fintype.card (Fin 2) := by rw [Fintype.card_fin]; norm_num
  have h := hpsd2.det_le_pow_trace_div_card hd2
  rw [hdet2, htr2, Fintype.card_fin] at h
  refine ⟨hdet2, htr2, ?_⟩
  simpa using h

/-- T4: the quadratic form differs from the unweighted squared norm. -/
example : ellipticalQuadratic ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (fun _ _ => 1) 0 = 1 / 2 ∧
    (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ (fun _ : Fin 1 => (1 : ℝ)) = 1 ∧
    ellipticalQuadratic ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ _ => 1)
      0 ≠ (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ (fun _ : Fin 1 => (1 : ℝ)) := by
  have hG0 : ellipticalGram ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (fun _ _ => 1) 0 = (2 : ℝ) • 1 :=
    ellipticalGram_zero _ _
  have hinv : ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = (2⁻¹ : ℝ) • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_assoc, one_mul, ← smul_assoc, smul_eq_mul,
      mul_inv_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num), one_smul]
  have hq : ellipticalQuadratic ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (fun _ _ => 1) 0 = 1 / 2 := by
    rw [ellipticalQuadratic, hG0, hinv, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul]
    simp [dotProduct, smul_eq_mul]
  have hu : (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
    simp [dotProduct]
  refine ⟨hq, hu, ?_⟩
  rw [hq, hu]; norm_num

-- T5: axiom checks for the five main theorems.
#print axioms Cslib.MachineLearning.LinearBandit.ellipticalGram_posDef
#print axioms Matrix.PosSemidef.det_le_pow_trace_div_card
#print axioms Cslib.MachineLearning.LinearBandit.sum_ellipticalPotential_le_two_log_det_ratio
#print axioms Cslib.MachineLearning.LinearBandit.log_det_ellipticalGram_ratio_le
#print axioms Cslib.MachineLearning.LinearBandit.elliptical_potential_lemma

end CSLibExtTest.MachineLearning.LinearBandit
