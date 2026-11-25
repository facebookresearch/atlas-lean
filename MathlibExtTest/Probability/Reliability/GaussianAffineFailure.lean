/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Reliability.GaussianAffineFailure
import MathlibExt.Probability.Distributions.GaussianCdf
import Mathlib.Tactic.NormNum

/-!
# Gaussian affine failure bracket checks

Focused checks for
`MathlibExt.Probability.Reliability.GaussianAffineFailure`:
the `a = 0` symmetry value for a coordinate functional, and the
combined bracket for an exactly affine limit-state function
with zero remainder.

These are elaboration and non-vacuity checks, not new results.
-/

open MeasureTheory ProbabilityTheory Set Reliability

/-- At zero intercept and threshold, a nonzero coordinate
functional has standard-Gaussian half-space mass `1 / 2`. -/
example :
    stdGaussian (EuclideanSpace ℝ (Fin 1))
        {z | (0 : ℝ)
          + innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) z
            ≤ 0}
      = ENNReal.ofReal (1 / 2 : ℝ) := by
  have hne : innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) ≠ 0 := by
    have hnorm : ‖innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))‖ = 1 := by
      rw [innerSL_apply_norm]
      exact EuclideanSpace.orthonormal_single.norm_eq_one 0
    intro h
    rw [h] at hnorm
    norm_num at hnorm
  rw [stdGaussian_affine_le_measure hne]
  simp [innerSL_apply_norm, cdf_gaussianReal_zero]

/-- Exactly affine `g` passes through the combined bracket with
zero remainder on the unit ball. -/
example :
    stdGaussian (EuclideanSpace ℝ (Fin 1))
          {z | (0 : ℝ)
            + innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) z
              ≤ 0}
        ≤ ENNReal.ofReal (cdf (gaussianReal 0 1) 0)
          + stdGaussian (EuclideanSpace ℝ (Fin 1))
              (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin 1)) 1)ᶜ
      ∧ ENNReal.ofReal (cdf (gaussianReal 0 1) 0)
        ≤ stdGaussian (EuclideanSpace ℝ (Fin 1))
            {z | (0 : ℝ)
              + innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) z
                ≤ 0}
          + stdGaussian (EuclideanSpace ℝ (Fin 1))
              (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin 1)) 1)ᶜ := by
  have hne : innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) ≠ 0 := by
    have hnorm : ‖innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))‖ = 1 := by
      rw [innerSL_apply_norm]
      exact EuclideanSpace.orthonormal_single.norm_eq_one 0
    intro h
    rw [h] at hnorm
    norm_num at hnorm
  have h := stdGaussian_affine_failure_bracket
    (g := fun z => (0 : ℝ)
      + innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) z)
    (L := innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
    hne (a := 0) (R := 1) (delta := 0) (fun z _ => by simp)
  simpa [innerSL_apply_norm] using h
