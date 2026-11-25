/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.RankineWall
import Mathlib.Tactic.NormNum

/-!
# Rankine wall checks

Focused checks for `PhyslibExt.EarthScience.Geotechnical.RankineWall`: for
`K_a = 1/3`, `γ = 18`, `H = 6`, the base pressure is 36, the
generic panel force and moment are 108 and 432, and the
resultant height above the base is 2.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience PhyslibExt.Mechanics.LinearPressurePanel

/-- Base pressure at the witness. -/
example : rankineActivePressure (1 / 3) 18 6 = 36 := by
  norm_num [rankineActivePressure]

/-- Force per unit wall length, through the generic panel
equation. -/
example : linearPressureForce (1 / 3 * 18) 1 0 6 = 108 := by
  rw [linearPressureForce_eq]
  norm_num

/-- Moment about the surface datum, through the generic panel
equation. -/
example : linearPressureMoment (1 / 3 * 18) 1 0 6 = 432 := by
  rw [linearPressureMoment_eq]
  norm_num

/-- Resultant height above the base: `6 - 432 / 108 = 2`. -/
example : (6 : ℝ) - linearPressureMoment (1 / 3 * 18) 1 0 6
    / linearPressureForce (1 / 3 * 18) 1 0 6 = 2 := by
  have h := rankine_resultant_height (Ka := 1 / 3) (γ := 18) (H := 6)
    (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num
