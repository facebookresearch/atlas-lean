/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.HolomorphicDiskDiameterDerivBound

/-! # Tests for the derivative bound by the diameter of the image -/

namespace MathlibExt.Analysis.Complex.HolomorphicDiskDiameterDerivBoundWanted

-- The identity map attains the bound, so the factor two is sharp.
example : Metric.ediam (Metric.ball (0 : ℂ) 1) = 2 := by
  apply le_antisymm
  · have h : Metric.ediam (Metric.ball (0 : ℂ) 1) ≤ ENNReal.ofReal 2 := by
      apply Metric.ediam_le_of_forall_dist_le
      intro z hz w hw
      rw [mem_ball_zero_iff] at hz hw
      exact (dist_le_norm_add_norm z w).trans (by linarith)
    simpa using h
  · simpa [deriv_id] using
      two_mul_norm_deriv_le_ediam_image_ball (id : ℂ → ℂ) differentiable_id.differentiableOn

-- Constant functions give the zero-diameter case.
example (c : ℂ) :
    Metric.ediam ((fun _ : ℂ => c) '' Metric.ball (0 : ℂ) 1) = 0 := by
  apply le_antisymm
  · exact Metric.ediam_image_le_iff.mpr (by simp)
  · have h := two_mul_norm_deriv_le_ediam_image_ball (fun _ : ℂ => c) (differentiableOn_const c)
    rwa [deriv_const, norm_zero, mul_zero, ENNReal.ofReal_zero] at h

end MathlibExt.Analysis.Complex.HolomorphicDiskDiameterDerivBoundWanted
