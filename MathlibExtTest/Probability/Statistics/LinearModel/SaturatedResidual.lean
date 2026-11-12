/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.SaturatedResidual

/-!
# Tests for `MathlibExt.Probability.Statistics.LinearModel.SaturatedResidual`

The identity design fits exactly; the RSS Dirac law applies under a normalized Gaussian
source; a rank-deficient square design is excluded.
-/

namespace MathlibExt.Probability.Statistics.LinearModel.SaturatedChecks

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

/-- Use case: identity design fits exactly, pointwise. -/
example (β ε : Fin 2 → ℝ) :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ β + ε -
      (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
        olsEstimator (1 : Matrix (Fin 2) (Fin 2) ℝ)
          ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ β + ε) = 0 := by
  have hX : IsUnit ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) := by
    rw [Matrix.transpose_one, Matrix.mul_one]
    exact isUnit_one
  have hM : residualMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 :=
    residualMatrix_eq_zero_of_square rfl hX
  rw [sub_mulVec_olsEstimator, hM, Matrix.zero_mulVec]

/-- Use case: the RSS Dirac law applies to the identity design under a normalized
Gaussian source (`Measure.count` has no probability instance and must not be used). -/
example (β : Fin 2 → ℝ) (ε : (Fin 1 → ℝ) → Fin 2 → ℝ) :
    HasLaw (fun x : Fin 1 → ℝ => ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ β + ε x -
        (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ olsEstimator (1 : Matrix (Fin 2) (Fin 2) ℝ)
          ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ β + ε x)) ⬝ᵥ
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ β + ε x -
        (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ olsEstimator (1 : Matrix (Fin 2) (Fin 2) ℝ)
          ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ β + ε x)))
      (Measure.dirac (0 : ℝ)) (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) := by
  have hX : IsUnit ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) := by
    rw [Matrix.transpose_one, Matrix.mul_one]
    exact isUnit_one
  exact hasLaw_rss_dirac_of_square rfl hX β ε

/-- Boundary: a rank-deficient square design is excluded. -/
example : ¬ IsUnit ((Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ))ᵀ *
    Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)) := by
  intro h
  have hdet : IsUnit (((Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ))ᵀ *
      Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp h
  have hentry : ∀ i j, (((Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ))ᵀ *
      Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)) i j) = 2 :=
    fun i j => by simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have hdet0 : (((Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ))ᵀ *
      Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)).det) = 0 := by
    rw [Matrix.det_fin_two, hentry 0 0, hentry 0 1, hentry 1 0, hentry 1 1]
    norm_num
  rw [hdet0] at hdet
  exact not_isUnit_zero hdet

end MathlibExt.Probability.Statistics.LinearModel.SaturatedChecks
