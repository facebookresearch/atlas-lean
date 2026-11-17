/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.FluidDynamics.Traffic.MovingFront

/-!
# Moving-front checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.MovingFront`: the
witness states `kL = 0, kR = 1, s = 1, qL = 0, qR = 1` satisfy the
balance with forced speed `1`, and `qR = 2` fails it.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic.MovingFront

/-- The witness balance and forced speed, through the public theorems. -/
example : (1 : ℝ) = ((1 : ℝ) - 0) / ((1 : ℝ) - 0) :=
  front_speed_eq_of_ne (by norm_num) (by norm_num)

/-- Both directions of the conservation form on the witness
(front at `8` inside `[0, 10]` at `t = 5`). -/
example : HasDerivAt (fun t => inventory 0 1 0 10 (1 * t + 3)) (0 - 1) 5
    ↔ (1 : ℝ) * (1 - 0) = 1 - 0 :=
  inventory_deriv_eq_iff_of_mem (by norm_num)

/-- A failed balance: slope is `-1`, not `0 - 2`. -/
example : ¬ HasDerivAt (fun t => inventory 0 1 0 10 (1 * t + 3)) (0 - 2) 5 := by
  rw [inventory_deriv_eq_iff_of_mem (show (0:ℝ) < 1 * 5 + 3 ∧ 1 * 5 + 3 < 10 by norm_num)]
  norm_num

/-- The interior form: front at `3` inside `[0, 10]` at time `0`. -/
example : HasDerivAt (fun t => inventory 0 1 0 10 (1 * t + 3)) (0 - 1) 0
    ↔ (1 : ℝ) * (1 - 0) = 1 - 0 :=
  inventory_deriv_eq_iff_of_mem (by norm_num)
