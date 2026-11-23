/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.FittedResidualIndependence
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Statistics.LinearModel.FittedResidualIndependence` -/

namespace MathlibExtTest.LinearModelFittedResidual

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

noncomputable def X₀ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun _ _ => 1

theorem gram_eq : X₀ᵀ * X₀ = !![(3 : ℝ)] := by
  ext i j
  fin_cases i; fin_cases j
  simp [X₀, Matrix.mul_apply]

theorem gram_isUnit : IsUnit (X₀ᵀ * X₀) := by
  rw [gram_eq, Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
  show IsUnit (3 : ℝ)
  rw [isUnit_iff_ne_zero]
  norm_num

theorem hat_eq : hatMatrix X₀ = Matrix.of fun _ _ => (1 : ℝ) / 3 := by
  ext i j
  simp [hatMatrix, olsMatrix,
    MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix,
    X₀, Matrix.mul_apply]

theorem hat_mul_residual : hatMatrix X₀ * residualMatrix X₀ = 0 :=
  hatMatrix_mul_residualMatrix gram_isUnit

theorem indepFun_fitted_residual_X₀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ε : Ω → Fin 3 → ℝ} {σ : ℝ} (β : Fin 1 → ℝ) (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω)
      (Measure.pi fun _ : Fin 3 => gaussianReal 0 1) μ) :
    IndepFun (fun ω => X₀ *ᵥ olsEstimator X₀ (X₀ *ᵥ β + ε ω))
      (fun ω => (X₀ *ᵥ β + ε ω) - X₀ *ᵥ olsEstimator X₀ (X₀ *ᵥ β + ε ω)) μ :=
  indepFun_fitted_residual (X := X₀) gram_isUnit β hσ hε

end MathlibExtTest.LinearModelFittedResidual
