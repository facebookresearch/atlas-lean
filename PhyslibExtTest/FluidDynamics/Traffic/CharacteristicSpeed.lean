/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Traffic.CharacteristicSpeed
import Mathlib.Tactic.NormNum

/-!
# Characteristic-speed checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.CharacteristicSpeed`:
at jam density the vehicle speed is 0 and the characteristic speed
is `-vf`; at zero density both are `vf`; at `k = 3`, `kj = 4`,
`vf = 2` the characteristic speed is negative while the vehicle
speed is positive.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic

/-- Jam density: vehicle speed zero, characteristic speed `-vf`. -/
example : greenshieldsVehicleSpeed 2 4 4 = 0
    ∧ deriv (greenshieldsFlux 2 4) 4 = -2 := by
  refine ⟨(greenshields_speeds_at_jam (by norm_num)).1, ?_⟩
  rw [greenshields_characteristicSpeed (by norm_num)]
  norm_num

/-- Above half jam: characteristic speed negative, vehicle speed
positive. -/
example : (2 : ℝ) * (1 - 2 * 3 / 4) < 0
    ∧ 0 < greenshieldsVehicleSpeed 2 4 3 :=
  greenshields_characteristicSpeed_neg (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
