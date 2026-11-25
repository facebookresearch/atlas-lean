/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.FiniteZerosInDiscOfHolomorphic

/-! # Tests for finite zeros in a disc -/

open MathlibExt.Analysis.Complex.FiniteZerosInDiscOfHolomorphicWanted

-- The rational function has a zero at the center, another on the boundary, and a pole at 4.
example : {z ∈ Metric.ball (0 : ℂ) 2 | z * (z - 2) / (z - 4) = 0}.Finite := by
  apply finite_zeros_in_ball_of_not_identically_zero (fun z => z * (z - 2) / (z - 4)) 0 2
    (by norm_num)
  · refine ⟨Metric.ball 0 3, Metric.isOpen_ball, Metric.closedBall_subset_ball (by norm_num), ?_⟩
    apply DifferentiableOn.div (by fun_prop) (by fun_prop)
    intro z hz hzero
    obtain rfl := sub_eq_zero.mp hzero
    norm_num [Metric.mem_ball, dist_zero_right] at hz
  · intro hall
    have h := hall 1 (by norm_num [Metric.mem_ball, dist_zero_right])
    norm_num at h
