/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.CSTR

import Mathlib.Tactic.NormNum

/-!
# Tests for the CSTR explicit solution

Boundary checks for `PhyslibExt.Engineering.Process.CSTR`: unit parameters
with inlet `2` and initial `0` give steady value `1` and profile
`1 - exp (-2t)`; zero flow is the batch branch; zero flow with zero rate is
constant.
-/

namespace Engineering.Process.CSTR.Tests

open Engineering.Process.CSTR

-- Q = V = k = 1, cin = 2, c0 = 0 gives css = 1 and c(t) = 1 - exp (-2t).
example : steady 1 1 1 2 = 1 := by
  unfold steady
  norm_num

example (t : ℝ) : solution 1 1 1 2 0 t = 1 - Real.exp (-2 * t) := by
  have hsteady : steady 1 1 1 2 = 1 := by unfold steady; norm_num
  have hrate : (1 : ℝ) / 1 + 1 = 2 := by norm_num
  unfold solution
  rw [hsteady, hrate]
  ring

example (t : ℝ) : |solution 1 1 1 2 0 t - 1| = Real.exp (-2 * t) := by
  have h := abs_sub_steady_eq 1 1 1 2 0 t
  have hsteady : steady 1 1 1 2 = 1 := by unfold steady; norm_num
  have hrate : (1 : ℝ) / 1 + 1 = 2 := by norm_num
  have habs : |(0 : ℝ) - 1| = 1 := by rw [zero_sub, abs_neg, abs_one]
  rw [hsteady, hrate] at h
  rw [h, habs, one_mul]

-- Q = k = 0 is the constant branch.
example (t : ℝ) : solution 1 0 0 2 5 t = 5 := by
  exact solution_zero_flow_zero_rate 1 2 5 t

-- Q = 0 with positive rate is the batch branch.
example (t : ℝ) : solution 2 0 3 7 4 t = 4 * Real.exp (-3 * t) := by
  have hV : (0 : ℝ) < 2 := by norm_num
  have hk : (0 : ℝ) < 3 := by norm_num
  exact solution_zero_flow hV hk

-- cin = 0 and c0 above the steady value 0.
example : solution 1 1 1 0 3 0 = 3 := by
  exact solution_initial 1 1 1 0 3

example (t : ℝ) (ht : 0 ≤ t) : 0 ≤ solution 1 1 1 0 3 t := by
  have hV : (0 : ℝ) < 1 := by norm_num
  have hQ : (0 : ℝ) < 1 := by norm_num
  have hk : (0 : ℝ) ≤ 1 := by norm_num
  have hcin : (0 : ℝ) ≤ 0 := by norm_num
  have hc0 : (0 : ℝ) ≤ 3 := by norm_num
  exact solution_nonneg hV hQ hk hcin hc0 ht

end Engineering.Process.CSTR.Tests
