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
# Front-speed checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.FrontSpeed`:
free states `kL = 10`, `kR = 40` (with `vf = 30`, `kj = 100`) give
front speed `15`; complementary densities `20`, `80` give a
stationary front.

These are elaboration and non-vacuity checks, not new results.
-/

/-- Free states: front speed `15`. -/
example : ((40 : ℝ) * (30 * (1 - 40 / 100)) - 10 * (30 * (1 - 10 / 100)))
      / (40 - 10)
    = 30 * (1 - (10 + 40) / 100) :=
  greenshields_front_speed (by norm_num) (by norm_num)

/-- Complementary densities: stationary front. -/
example : (80 : ℝ) * (30 * (1 - 80 / 100)) - 20 * (30 * (1 - 20 / 100))
      = 0 := by
  have h := greenshields_front_speed (vf := 30) (kj := 100) (kL := 20)
    (kR := 80) (by norm_num) (by norm_num)
  rw [show (30 : ℝ) * (1 - (20 + 80) / 100) = 0 by norm_num] at h
  have hdiv : ((80 : ℝ) * (30 * (1 - 80 / 100))
      - 20 * (30 * (1 - 20 / 100))) / (80 - 20) = 0 := h
  have := (div_eq_zero_iff).1 hdiv
  rcases this with h1 | h1
  · exact h1
  · norm_num at h1
