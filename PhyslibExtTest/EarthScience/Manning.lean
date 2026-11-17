/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.Manning

/-!
# Manning monotonicity checks

Focused checks for `PhyslibExt.EarthScience.Manning`: at unit geometry,
quadrupling the slope doubles the discharge (square-root scaling), and
doubling the roughness halves it.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Quadrupling slope doubles discharge at unit geometry. -/
example : manningDischarge 1 1 1 4 = 2 := by
  have h : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  norm_num [manningDischarge, h]

/-- Slope comparison through the public theorem. -/
example : manningDischarge 1 1 1 1 < manningDischarge 1 1 1 4 :=
  manningDischarge_lt_of_slope_lt (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Doubling roughness halves discharge at unit geometry. -/
example : manningDischarge 2 1 1 1 = 1 / 2 := by
  norm_num [manningDischarge]

/-- Roughness comparison through the public theorem. -/
example : manningDischarge 2 1 1 1 < manningDischarge 1 1 1 1 :=
  manningDischarge_lt_of_roughness_lt (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
