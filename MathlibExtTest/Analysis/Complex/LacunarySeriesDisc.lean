/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Complex.LacunarySeriesDisc

/-! # Interior and boundary values of the lacunary series -/

open MathlibExt.Analysis.Complex.LacunarySeriesDiscWanted
open scoped Topology

example : f 0 = 0 := by
  simp [f, zero_pow (pow_ne_zero _ two_ne_zero)]

example : DifferentiableAt ℂ f 0 := by
  exact differentiableOn_ball_continuousOn_closedBall_lacunary.1.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))

-- At the boundary point 1, the series reduces to the geometric sum 2.
example : Filter.Tendsto f (𝓝[Metric.closedBall (0 : ℂ) 1] 1) (𝓝 2) := by
  have hvalue : f 1 = 2 := by
    simp only [f, one_pow, mul_one]
    rw [tsum_geometric_of_norm_lt_one (by norm_num [norm_div, Complex.norm_two])]
    norm_num
  have hc := differentiableOn_ball_continuousOn_closedBall_lacunary.2
  rw [closure_ball 0 one_ne_zero] at hc
  rw [← hvalue]
  exact hc 1 (mem_closedBall_zero_iff.mpr (by simp))
