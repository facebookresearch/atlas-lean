/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.StdGaussianHyperplane

@[expose] public section

open Real MeasureTheory ProbabilityTheory
  MathlibExt.Probability.Distributions.StdGaussianHyperplane

namespace MathlibExtTest.Probability.Distributions.StdGaussianHyperplane

/-- Lines at angle `π / 2` (`a = π / 4`) separate a planar standard Gaussian point with
probability `1 / 2`. -/
example : (gaussianReal 0 1).prod (gaussianReal 0 1)
    {p : ℝ × ℝ | (0 ≤ cos (π / 4) * p.1 - sin (π / 4) * p.2) ≠
      (0 ≤ cos (π / 4) * p.1 + sin (π / 4) * p.2)} = ENNReal.ofReal (1 / 2) := by
  rw [gaussianReal_prod_wedge (by positivity) (by linarith [pi_pos])]
  congr 1
  field_simp
  norm_num

/-- Orthogonal unit vectors are separated with probability `1 / 2`. -/
example : stdGaussian (EuclideanSpace ℝ (Fin 2))
    {r | (0 ≤ inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) r) ≠
      (0 ≤ inner ℝ (EuclideanSpace.single 1 (1 : ℝ)) r)} = ENNReal.ofReal (1 / 2) := by
  rw [stdGaussian_sign_ne (by simp) (by simp)]
  simp [EuclideanSpace.inner_single_left, arccos_zero]
  rw [show π / 2 / π = (2 : ℝ)⁻¹ by field_simp, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- A unit vector is never separated from itself. -/
example (u : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ = 1) :
    stdGaussian (EuclideanSpace ℝ (Fin 3)) {r | (0 ≤ inner ℝ u r) ≠ (0 ≤ inner ℝ u r)} = 0 := by
  rw [stdGaussian_sign_ne hu hu, real_inner_self_eq_norm_sq, hu]
  simp

end MathlibExtTest.Probability.Distributions.StdGaussianHyperplane
