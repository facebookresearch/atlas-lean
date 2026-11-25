/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.StripBoundedHolomorphicGrowth

open MathlibExt.Analysis.Complex.StripBoundedHolomorphicGrowthWanted

/-- The identity is a normalized holomorphic map from the disk into the vertical strip. -/
example (z : ℂ) (hz : z ∈ D) :
    ‖z‖ ≤ (2 / Real.pi) * Real.log ((1 + ‖z‖) / (1 - ‖z‖)) := by
  apply norm_le_two_div_pi_mul_log_of_abs_re_lt_one id differentiableOn_id rfl _ z hz
  intro w hw
  exact (Complex.abs_re_le_norm w).trans_lt (mem_ball_zero_iff.mp hw)
