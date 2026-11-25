/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.CenterOfPressure

/-!
# Center-of-pressure checks

Focused checks for `PhyslibExt.Mechanics.CenterOfPressure`: the
free-surface value `2 * H / 3` (for `H = 3`, depth 2), and the
submerged panel `[1, 2]` whose center `14 / 9` lies in `[1, 2]`.

These are elaboration and non-vacuity checks, not new results.
-/

open PhyslibExt.Mechanics.LinearPressurePanel

/-- Free-surface panel with `H = 3`: center at depth 2. -/
example : linearPressureMoment 1 1 0 3 / linearPressureForce 1 1 0 3
    = 2 := by
  have h := centerOfPressure_freeSurface (c := 1) (w := 1) (H := 3)
    (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

/-- Submerged panel `[1, 2]`: center in the interval. -/
example : linearPressureMoment 1 1 1 2 / linearPressureForce 1 1 1 2
    ∈ Set.Icc (1 : ℝ) 2 :=
  centerOfPressure_mem (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
