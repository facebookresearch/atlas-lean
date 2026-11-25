/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.RecursiveLeastSquares
public import CSLibExt.MachineLearning.Regression.LeastSquares

/-!
# Recursive least squares computes ridge regression

With initial estimate `θ_0 = 0` and initial matrix `P_0 = λ⁻¹ I` (`λ > 0`), the recursive
least-squares estimate after `t` observations is the ridge-regression estimate
`(Xᵀ X + λ I)⁻¹ Xᵀ Y` of the design `X` with rows `φ_0, …, φ_{t-1}` and responses
`Y = (y_1, …, y_t)`, hence the unique minimiser of `|Y - X θ|² + λ |θ|²`. This identifies the
recursion of `MathlibExt.Analysis.Control.RecursiveLeastSquares` with the batch least-squares
problem of `Cslib.MachineLearning.LeastSquares`.
-/

@[expose] public section

open Matrix

namespace Cslib.MachineLearning.RecursiveLeastSquares

open MathlibExt.Analysis.Control.RecursiveLeastSquares Cslib.MachineLearning.LeastSquares

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Design matrix of the first `t` regressors.** The matrix with rows `φ_0, …, φ_{t-1}`. -/
def designMatrix (φ : ℕ → n → ℝ) (t : ℕ) : Matrix (Fin t) n ℝ :=
  Matrix.of fun k i => φ k i

omit [Fintype n] [DecidableEq n] in
theorem designMatrix_transpose_mul (φ : ℕ → n → ℝ) (t : ℕ) :
    (designMatrix φ t)ᵀ * designMatrix φ t =
      ∑ k ∈ Finset.range t, vecMulVec (φ k) (φ k) := by
  ext i j
  simp only [mul_apply, transpose_apply, designMatrix, of_apply, Matrix.sum_apply,
    vecMulVec_apply]
  exact Fin.sum_univ_eq_sum_range (fun k => φ k i * φ k j) t

omit [Fintype n] [DecidableEq n] in
theorem designMatrix_transpose_mulVec (φ : ℕ → n → ℝ) (y : ℕ → ℝ) (t : ℕ) :
    (designMatrix φ t)ᵀ *ᵥ (fun k : Fin t => y (k + 1)) =
      ∑ k ∈ Finset.range t, y (k + 1) • φ k := by
  ext i
  simp only [mulVec, dotProduct, transpose_apply, designMatrix, of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun k => y (k + 1) * φ k i) t]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Recursive least squares started at `θ_0 = 0`, `P_0 = λ⁻¹ I` is ridge regression.** For
`λ > 0` and every `t`, the RLS estimate `θ_t` equals the ridge estimate
`(Xᵀ X + λ I)⁻¹ Xᵀ Y` of the design `X` with rows `φ_0, …, φ_{t-1}` and responses
`Y_k = y_{k+1}`. -/
theorem rls_fst_eq_ridgeEstimate (φ : ℕ → n → ℝ) (y : ℕ → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (t : ℕ) :
    (rls φ y 0 (lam⁻¹ • (1 : Matrix n n ℝ)) t).1 =
      ridgeEstimate (designMatrix φ t) (fun k : Fin t => y (k + 1)) lam := by
  have hP₀ : (lam⁻¹ • (1 : Matrix n n ℝ)).PosDef := PosDef.one.smul (inv_pos.mpr hlam)
  have hinv : (lam⁻¹ • (1 : Matrix n n ℝ))⁻¹ = lam • 1 := by
    apply inv_eq_right_inv
    rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ hlam.ne', one_smul]
  rw [rls_fst_eq hP₀, ridgeEstimate, designMatrix_transpose_mul, designMatrix_transpose_mulVec,
    rlsInformation, hinv, mulVec_zero, zero_add, add_comm]

/-- **The RLS estimate minimises the ridge objective.** For `λ > 0`, the RLS estimate started
at `θ_0 = 0` and `P_0 = λ⁻¹ I` minimises `∑_{k<t} (y_{k+1} - φ_kᵀ θ)² + λ |θ|²` over all `θ`. -/
theorem ridge_le_rls_fst (φ : ℕ → n → ℝ) (y : ℕ → ℝ) {lam : ℝ} (hlam : 0 < lam) (t : ℕ)
    (θ : n → ℝ) :
    ridge (designMatrix φ t) (fun k : Fin t => y (k + 1)) lam
        (rls φ y 0 (lam⁻¹ • (1 : Matrix n n ℝ)) t).1 ≤
      ridge (designMatrix φ t) (fun k : Fin t => y (k + 1)) lam θ := by
  rw [rls_fst_eq_ridgeEstimate φ y hlam]
  exact ridge_le_ridgeEstimate _ _ hlam θ

end Cslib.MachineLearning.RecursiveLeastSquares
