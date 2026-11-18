/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.RankineWall

/-!
# Rankine wall checks

Focused checks for `PhyslibExt.Mechanics.RankineWall`: for
`K_a = 1/3`, `γ = 18`, `H = 6`, the force per unit length is 108,
the moment is 432, and the resultant height above the base is 2.

These are elaboration and non-vacuity checks, not new results.
-/

open PhyslibExt.Mechanics.LinearPressurePanel

/-- Force per unit wall length. -/
example : linearPressureForce (1 / 3 * 18) 1 0 6 = 108 := by
  rw [rankine_force]
  norm_num

/-- Resultant height above the base: `6 - 432 / 108 = 2`. -/
example : (6 : ℝ) - linearPressureMoment (1 / 3 * 18) 1 0 6
    / linearPressureForce (1 / 3 * 18) 1 0 6 = 2 := by
  have h := rankine_resultant_height (Ka := 1 / 3) (γ := 18) (H := 6)
    (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num
