/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Statistics.RestrictedLikelihood.AverageInformation
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests of average information

The first example isolates a mixed entry for two noncommuting components, with a third
component making their sum `4I`. The second has positive definite covariance but identical
components: its nonzero average information nevertheless has determinant zero.
-/

open Matrix MathlibExt.Probability.Statistics.LinearModel.AverageInformation

namespace MathlibExtTest.REMLAverageInformation

private abbrev M := Matrix (Fin 3) (Fin 3) ℝ
private noncomputable def A : Fin 3 → M :=
  ![!![1,0,0;0,0,0;0,0,0], !![1,1,0;1,1,0;0,0,0], !![2,-1,0;-1,3,0;0,0,4]]
private noncomputable def X : Matrix (Fin 3) (Fin 1) ℝ := !![0;0;1]
private noncomputable def σ : Fin 3 → ℝ := fun _ => 1
private noncomputable def y : Fin 3 → ℝ := ![1,0,0]

private theorem cov : covarianceAt A σ = diagonal (fun _ => (4 : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [covarianceAt, A, σ, Fin.sum_univ_succ, diagonal]

private theorem rankX : Function.Injective X.mulVec := by
  intro u v h; ext i; fin_cases i
  simpa [X, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun h 2

private theorem invConstDiag {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℝ) (ha : a ≠ 0) :
    (diagonal (fun _ : ι => a))⁻¹ = diagonal (fun _ => a⁻¹) := by
  apply inv_eq_left_inv
  rw [diagonal_mul_diagonal]; simp [ha]

private theorem prec : precision X (covarianceAt A σ) = diagonal ![1/4,1/4,0] := by
  rw [cov, precision, invConstDiag _ (by norm_num)]
  have hG : Xᵀ * diagonal (fun _ : Fin 3 => (4 : ℝ)⁻¹) * X = diagonal (fun _ => 1/4) := by
    ext i j; fin_cases i; fin_cases j
    simp only [Matrix.mul_apply, transpose_apply, diagonal_apply, Fin.sum_univ_succ]
    norm_num [X]
  rw [hG, invConstDiag _ (by norm_num)]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [X, Matrix.mul_apply, Fin.sum_univ_succ,
    diagonal, transpose_apply, Matrix.vecHead, vecMul, dotProduct, Function.swap]

/-- The first score and the three mixed information entries at the noncommuting fixture.
The observed entry is negative and the average is one quarter of the expectation. -/
private theorem noncommuting_mixed_entry : A 0 * A 1 ≠ A 1 * A 0 ∧ score X A σ y 0 = -3/32 ∧
    observed X A σ y 0 1 = -1/64 ∧
    fisher X A σ 0 0 1 = 1/32 ∧ average X A σ y 0 0 1 = 1/128 := by
  have hv : (covarianceAt A σ).PosDef := by rw [cov]; exact PosDef.diagonal (by intros; norm_num)
  have hs (i : Fin 3) : (A i)ᵀ = A i := by
    ext j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl
  have sc := score_eq X A σ hv rankX y 0
  have ho := observed_eq X A σ hv rankX hs y 0 1
  have hf := fisher_eq X A σ hv rankX hs 0 0 1
  dsimp only at sc ho hf
  rw [prec] at sc ho hf
  norm_num [A, y, Matrix.trace, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_succ,
    diagonal] at sc ho hf
  change score X A σ y 0 = -(3/32) at sc
  change observed X A σ y 0 1 = -(1/64) at ho
  change fisher X A σ 0 0 1 = 1/32 at hf
  refine ⟨?_, by linarith, by linarith, hf, ?_⟩
  · intro h; have hh := congrFun (congrFun h 0) 1
    norm_num [A, Matrix.mul_apply, Fin.sum_univ_succ] at hh
  · change (observed _ _ _ _ _ _ + fisher _ _ _ _ _ _) / 2 = _; rw [ho, hf]; norm_num

/-- Two copies of the identity at weights `1/2`, with an intercept and response `(1,-1)`,
give positive definite covariance and an all-ones, hence singular, average-information matrix. -/
private theorem repeated_components : let B := fun _ : Fin 2 => (1 : Matrix (Fin 2) (Fin 2) ℝ)
    let τ := fun _ : Fin 2 => (1/2 : ℝ)
    let Z : Matrix (Fin 2) (Fin 1) ℝ := !![1;1]
    let u : Fin 2 → ℝ := ![1,-1]
    (covarianceAt B τ).PosDef ∧ average Z B τ u 0 = !![1,1;1,1] ∧ (average Z B τ u 0).det = 0 := by
  intro B τ Z u
  have hv : covarianceAt B τ = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [covarianceAt, B, τ, Fin.sum_univ_succ, Matrix.one_apply]
  have hz : Function.Injective Z.mulVec := by
    intro a b h; ext i; fin_cases i; simpa [Z, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun h 0
  have hg : Zᵀ * Z = diagonal (fun _ => (2 : ℝ)) := by
    ext i j; fin_cases i; fin_cases j; norm_num [Z, Matrix.mul_apply, Fin.sum_univ_succ, diagonal]
  have hv' : (covarianceAt B τ).PosDef := hv ▸ PosDef.one
  have hm := (average_eq_gram Z B τ hv' hz (by simp [B]) u 0).1
  have hp : precision Z (covarianceAt B τ) = !![1/2, -1/2; -1/2, 1/2] := by
    simp only [precision, hv, inv_one, Matrix.mul_one, Matrix.one_mul, hg, invConstDiag 2 (by norm_num)]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Z, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
        transpose_apply, diagonal, Function.swap, vecMul, dotProduct, Matrix.vecHead]
  have mat : average Z B τ u 0 = !![1,1;1,1] := by
    rw [hm, hp]; simp only [B, one_mulVec]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [u, Matrix.mul_apply, mulVec, vecMul, dotProduct, Fin.sum_univ_succ, transpose_apply,
        Function.swap]
  exact ⟨hv', mat, by rw [mat, det_fin_two_of]; norm_num⟩

end MathlibExtTest.REMLAverageInformation
