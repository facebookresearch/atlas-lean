/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Traffic.FrontSpeed
import Mathlib.Tactic.NormNum

/-!
# Shock-speed checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.FrontSpeed`:
free states `kL = 10`, `kR = 40` (with `vf = 30`, `kj = 100`) give
shock speed `15`; complementary densities `20`, `80` give a
stationary front.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic

/-- Free states: shock speed `15`. -/
example : ShockOrdering.shockSpeed (greenshieldsFlux 30 100) 10 40
    = 30 * (1 - (10 + 40) / 100) :=
  greenshields_shock_speed (by norm_num) (by norm_num)

/-- Complementary densities: stationary front. -/
example : ShockOrdering.shockSpeed (greenshieldsFlux 30 100) 20 80 = 0 := by
  rw [greenshields_shock_speed (kj := (100 : ℝ)) (by norm_num) (by norm_num)]
  norm_num
