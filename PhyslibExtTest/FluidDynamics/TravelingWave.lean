/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.FluidDynamics.TravelingWave

/-!
# Traveling-wave checks

Focused checks for `PhyslibExt.FluidDynamics.TravelingWave`: with
`F = id`, `rho = g = A = a = 1`, the right jump between `x = 0` and
`x = 1` is `1 = 1 * 1`, and the left jump is `1 = -1 * (-1)`.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.TravelingWave

/-- Right jump for the identity profile. -/
example : (1:ℝ) * 1 * (hR 1 id 0 1 - hR 1 id 0 0)
    = 1 * 1 * ((qR 1 1 1 id 0 1 - qR 1 1 1 id 0 0) / 1) :=
  jump_right (by norm_num) (by norm_num) id 0 0 1

/-- Left jump for the identity profile. -/
example : (1:ℝ) * 1 * (hL 1 id 0 1 - hL 1 id 0 0)
    = - 1 * 1 * ((qL 1 1 1 id 0 1 - qL 1 1 1 id 0 0) / 1) :=
  jump_left (by norm_num) (by norm_num) id 0 0 1
