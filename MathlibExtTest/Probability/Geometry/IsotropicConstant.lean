/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Geometry.IsotropicCube

open MathlibExt.Probability.IsotropicConstant MathlibExt.Probability.ThinShell MeasureTheory
open scoped ENNReal

example : IsIsotropicLogConcave (uniformInterval (Real.sqrt 3)) :=
  uniformInterval_sqrt_three_isIsotropicLogConcave

example : covarianceMatrix (uniformInterval (Real.sqrt 3)) = 1 :=
  covarianceMatrix_eq_one_of_isIsotropic uniformInterval_sqrt_three_isIsotropicLogConcave

example : IsProbabilityMeasure (bodyLaw unitIntervalBody) :=
  bodyLaw_probability unitIntervalBody

example : IsProbabilityMeasure (bodyIntrinsicLogConcaveLaw unitIntervalBody).law :=
  intrinsicLaw_probability (bodyIntrinsicLogConcaveLaw unitIntervalBody)

example : volume (unitIntervalBody.body : Set (EuclideanSpace ℝ (Fin 1))) = 1 :=
  unitIntervalBody_volume

example : (covarianceMatrix (bodyLaw unitIntervalBody)).det = 1 / 12 :=
  unitIntervalBody_covariance_det

example : (covarianceMatrix (bodyLaw unitIntervalBody)).PosSemidef :=
  covarianceMatrix_posSemidef (bodyLogConcaveLaw unitIntervalBody)

example : differentialEntropy (bodyDensity unitIntervalBody) = 0 := unitIntervalBody_entropy

example : bodyIsotropicConstant unitIntervalBody = 1 / Real.sqrt 12 :=
  unitIntervalBody_isotropicConstant

example : intrinsicLawIsotropicConstant (bodyIntrinsicLogConcaveLaw unitIntervalBody) =
    bodyIsotropicConstant unitIntervalBody := bodyIntrinsicLaw_isotropicConstant unitIntervalBody

example : IsCentrallySymmetric unitIntervalBody := unitIntervalBody_isCentrallySymmetric

example : ENNReal.ofReal (1 / Real.sqrt 12) ≤ centrallySymmetricBodySupremum :=
  inv_sqrt_twelve_le_centrallySymmetricBodySupremum

example : ENNReal.ofReal (1 / Real.sqrt 12) ≤ entropyIsotropicConstant :=
  inv_sqrt_twelve_le_entropyIsotropicConstant

example : bodySupremum ≤ entropyIsotropicConstant := bodySupremum_le_entropyIsotropicConstant

example : (covarianceMatrix (bodyLaw unitIntervalBody)).det ≠ 1 := by
  rw [unitIntervalBody_covariance_det]
  norm_num

example : ¬ Nonempty (LogConcaveLaw 0) := by
  rintro ⟨μ⟩
  exact (Nat.lt_irrefl 0) μ.dimension_pos

example : ¬ IsIsotropicLogConcave (uniformInterval 1) :=
  uniformInterval_one_not_isIsotropicLogConcave
