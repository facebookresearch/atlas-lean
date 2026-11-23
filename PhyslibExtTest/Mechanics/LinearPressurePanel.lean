/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Mechanics.LinearPressurePanel

/-!
# Linear-pressure checks

Focused checks for `PhyslibExt.Mechanics.LinearPressurePanel`: at
`c = w = 1` on `[0, 2]` the force is `2`, the moment is `8 / 3`, and the
resultant acts at depth `4 / 3`; a nonzero-lower-bound interval
`[1, 4]` gives force `15 / 2`.

These are elaboration and non-vacuity checks, not new results.
-/

open PhyslibExt.Mechanics.LinearPressurePanel

/-- Force and moment on `[0, 2]`, through the public theorems. -/
example : linearPressureForce 1 1 0 2 = 2 ∧ linearPressureMoment 1 1 0 2 = 8 / 3 := by
  constructor
  · rw [linearPressureForce_eq]; norm_num
  · rw [linearPressureMoment_eq]; norm_num

/-- Nonzero-lower-bound interval `[1, 4]`. -/
example : linearPressureForce 1 1 1 4 = 15 / 2 := by
  rw [linearPressureForce_eq]; norm_num
