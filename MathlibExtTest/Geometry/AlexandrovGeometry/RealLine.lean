/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.AlexandrovGeometry.RealLine
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tests for degenerate model angles and the real line

Verifies `isAlex_real` at `κ = 1, 0, -1` and the degenerate-angle
theorems at concrete side lengths.
-/

open AlexandrovGeometry

/-- The real line is `Alex 1` (no diameter bound for `κ > 0`). -/
theorem test_isAlex_one : IsAlex 1 ℝ := isAlex_real 1

/-- The real line is `Alex 0`. -/
theorem test_isAlex_zero : IsAlex 0 ℝ := isAlex_real 0

/-- The real line is `Alex (-1)`. -/
theorem test_isAlex_neg : IsAlex (-1) ℝ := isAlex_real (-1)

/-- Straight `κ = 1` triangle on sides `1, 2` has angle `π`. -/
theorem test_add_eq_pi (hdef : ModelTriangleDefined 1 (1 + 2) 1 2) :
    modelAngle 1 (1 + 2) 1 2 = Real.pi :=
  modelAngle_add_eq_pi 1 1 2 (by norm_num) (by norm_num) hdef

/-- The `κ = 1` straight instance above is defined. -/
theorem test_def_one : ModelTriangleDefined 1 (1 + 2) 1 2 := by
  unfold ModelTriangleDefined
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro _
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  simp only [Real.sqrt_one]
  linarith [hpi]

/-- Closed `κ = 1` straight instance: the angle is `π`. -/
theorem test_add_closed : modelAngle 1 (1 + 2) 1 2 = Real.pi :=
  modelAngle_add_eq_pi 1 1 2 (by norm_num) (by norm_num) test_def_one

/-- Flat `κ = -1` triangle on sides `1, 3` has angle `0`. -/
theorem test_abs_sub_eq_zero (hdef : ModelTriangleDefined (-1) |1 - 3| 1 3) :
    modelAngle (-1) |1 - 3| 1 3 = 0 :=
  modelAngle_abs_sub_eq_zero (-1) 1 3 (by norm_num) (by norm_num) hdef

/-- The `κ = -1` flat instance above is defined. -/
theorem test_def_neg : ModelTriangleDefined (-1) |1 - 3| 1 3 := by
  unfold ModelTriangleDefined
  refine ⟨by norm_num, by norm_num, by norm_num, fun h => absurd h (by norm_num)⟩

/-- Closed `κ = -1` flat instance: the angle is `0`. -/
theorem test_abs_sub_closed : modelAngle (-1) |1 - 3| 1 3 = 0 :=
  modelAngle_abs_sub_eq_zero (-1) 1 3 (by norm_num) (by norm_num) test_def_neg
