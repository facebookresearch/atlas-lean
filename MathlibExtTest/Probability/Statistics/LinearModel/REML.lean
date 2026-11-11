/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.REML
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Statistics.LinearModel.REML`

Intercept-only design with three observations (one cluster). Two error contrasts:
the successive-difference contrast `A` and the centering contrast `B` (the first two rows of
`1 - J / 3`). They satisfy `B = Q A` with `det Q = 1 / 3`, so `ℓ_B = ℓ_A + log 3`. This is
checked against the general theorem and, independently, by evaluating both closed forms at
`V = 1`, `y = 0`. At the singular covariance `V = 0`, both criteria take the junk value `0`
and the identity fails, so the positive-definiteness hypothesis is necessary.
-/

open Matrix MeasureTheory ProbabilityTheory WithLp MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExtTest.LinearModelREML

/-- Intercept-only design with three observations. -/
noncomputable def X₀ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- Successive-difference contrast: `(y₀ - y₁, y₁ - y₂)`. -/
noncomputable def A₀ : Matrix (Fin 2) (Fin 3) ℝ := !![1, -1, 0; 0, 1, -1]

/-- Centering contrast: the first two rows of `1 - J / 3`, i.e. `(y₀ - ȳ, y₁ - ȳ)`. -/
noncomputable def B₀ : Matrix (Fin 2) (Fin 3) ℝ := !![2/3, -1/3, -1/3; -1/3, 2/3, -1/3]

/-- The change of basis from `A₀` to `B₀`. -/
noncomputable def Q₀ : Matrix (Fin 2) (Fin 2) ℝ := !![2/3, 1/3; -1/3, 1/3]

theorem isUnit_gram_X₀ : IsUnit (X₀ᵀ * X₀) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
  simp [X₀, Matrix.mul_apply]

theorem A₀_mul_transpose : A₀ * A₀ᵀ = !![2, -1; -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A₀, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem B₀_mul_transpose : B₀ * B₀ᵀ = !![2/3, -1/3; -1/3, 2/3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B₀, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem isErrorContrast_A₀ : IsErrorContrast X₀ A₀ where
  mul_eq_zero := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A₀, X₀, Matrix.mul_apply, Fin.sum_univ_succ]
  isUnit_mul_transpose := by
    rw [Matrix.isUnit_iff_isUnit_det, A₀_mul_transpose, Matrix.det_fin_two_of]; norm_num
  card_add_card := by simp

theorem isErrorContrast_B₀ : IsErrorContrast X₀ B₀ where
  mul_eq_zero := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [B₀, X₀, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      norm_num
  isUnit_mul_transpose := by
    rw [Matrix.isUnit_iff_isUnit_det, B₀_mul_transpose, Matrix.det_fin_two_of]; norm_num
  card_add_card := by simp

theorem B₀_eq : B₀ = Q₀ * A₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A₀, B₀, Q₀, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    norm_num

theorem det_Q₀ : Q₀.det = 1 / 3 := by
  rw [Q₀, Matrix.det_fin_two_of]; norm_num

/-- The general uniqueness theorem applies to the fixture. -/
example : ∃ Q : Matrix (Fin 2) (Fin 2) ℝ, IsUnit Q.det ∧ B₀ = Q * A₀ :=
  exists_eq_mul_of_isErrorContrast isUnit_gram_X₀ isErrorContrast_A₀ isErrorContrast_B₀

/-- **Fixture, general covariance**: centering and differencing give REML criteria that differ by
exactly `log 3`, for every positive definite `V` and every `y`. -/
theorem remlLogLik_B₀ {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : V.PosDef) (y : Fin 3 → ℝ) :
    remlLogLik B₀ V y = remlLogLik A₀ V y + Real.log 3 := by
  rw [B₀_eq, remlLogLik_mul_left (posDef_mul_mul_transpose hV
      isErrorContrast_A₀.isUnit_mul_transpose) (by rw [det_Q₀]; norm_num), det_Q₀,
    abs_of_pos (by norm_num), one_div, Real.log_inv, sub_neg_eq_add]

/-- Direct evaluation of `ℓ_A` at `V = 1`, `y = 0` from the closed form: `det (A Aᵀ) = 3`. -/
theorem remlLogLik_A₀_one_zero :
    remlLogLik A₀ 1 0 = -Real.log (2 * Real.pi) - Real.log 3 / 2 := by
  rw [remlLogLik_eq (posDef_mul_mul_transpose Matrix.PosDef.one
    isErrorContrast_A₀.isUnit_mul_transpose), Matrix.mul_one, A₀_mul_transpose,
    Matrix.det_fin_two_of]
  simp
  norm_num

/-- Direct evaluation of `ℓ_B` at `V = 1`, `y = 0` from the closed form: `det (B Bᵀ) = 1/3`. -/
theorem remlLogLik_B₀_one_zero :
    remlLogLik B₀ 1 0 = -Real.log (2 * Real.pi) + Real.log 3 / 2 := by
  rw [remlLogLik_eq (posDef_mul_mul_transpose Matrix.PosDef.one
    isErrorContrast_B₀.isUnit_mul_transpose), Matrix.mul_one, B₀_mul_transpose,
    Matrix.det_fin_two_of]
  have h : (2 / 3 * (2 / 3) - -1 / 3 * (-1 / 3) : ℝ) = 3⁻¹ := by norm_num
  simp only [h, Real.log_inv, mulVec_zero, dotProduct_zero, zero_div, sub_zero]
  simp
  ring

/-- The direct evaluations agree with `remlLogLik_B₀`: the difference is `log 3`. -/
example : remlLogLik B₀ 1 0 - remlLogLik A₀ 1 0 = Real.log 3 := by
  rw [remlLogLik_B₀_one_zero, remlLogLik_A₀_one_zero]; ring

/-- **Singular covariance is excluded, not totalized.** At `V = 0` both criteria take the junk
value `log 0 = 0`, so `ℓ_B = ℓ_A + log 3` fails: the hypothesis `V.PosDef` is necessary. -/
theorem remlLogLik_zero_cov (A : Matrix (Fin 2) (Fin 3) ℝ) (y : Fin 3 → ℝ) :
    remlLogLik A 0 y = 0 := by
  simp [remlLogLik, MetaMathlibExt.multivariateGaussianPDFReal]

example : remlLogLik B₀ 0 0 ≠ remlLogLik A₀ 0 0 + Real.log 3 := by
  rw [remlLogLik_zero_cov, remlLogLik_zero_cov, zero_add]
  exact (Real.log_pos (by norm_num)).ne

/-- Law of the centering contrast: if `y ~ N(X₀ β, V)`, then `B₀ y ~ N(0, B₀ V B₀ᵀ)`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {V : Matrix (Fin 3) (Fin 3) ℝ}
    (hV : V.PosSemidef) (β : Fin 1 → ℝ) {y : Ω → EuclideanSpace ℝ (Fin 3)}
    (hy : HasLaw y (multivariateGaussian (toLp 2 (X₀ *ᵥ β)) V) μ) :
    HasLaw (fun ω => toEuclideanLin B₀ (y ω)) (multivariateGaussian 0 (B₀ * V * B₀ᵀ)) μ :=
  hasLaw_errorContrast isErrorContrast_B₀.mul_eq_zero hV β hy

/-- Argmax invariance on the fixture, for a one-parameter family `V θ = exp θ • 1`. -/
example (y : Fin 3 → ℝ) (s : Set ℝ) (θ₀ : ℝ) :
    IsMaxOn (fun θ => remlLogLik B₀ (Real.exp θ • 1) y) s θ₀ ↔
      IsMaxOn (fun θ => remlLogLik A₀ (Real.exp θ • 1) y) s θ₀ := by
  rw [B₀_eq]
  exact isMaxOn_remlLogLik_mul_left_iff isErrorContrast_A₀.isUnit_mul_transpose
    (fun θ => Matrix.PosDef.one.smul (Real.exp_pos θ)) (by rw [det_Q₀]; norm_num) y s θ₀

end MathlibExtTest.LinearModelREML
