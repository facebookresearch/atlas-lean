/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.ClassicalMechanics.Acoustics.PressureLevel

/-!
# Pressure-level checks

Focused checks for `PhyslibExt.ClassicalMechanics.Acoustics.PressureLevel`:
a tenfold pressure ratio gives 20 dB, and matched references give
0 dB.

These are elaboration and non-vacuity checks, not new results.
-/

open Acoustics

/-- Tenfold pressure ratio is 20 dB. -/
example : intensityLevel (1 ^ 2 / 1) (10 ^ 2 / 1)
    = 20 * Real.logb 10 (10 / 1) :=
  intensityLevel_eq_pressureLevel (by norm_num) (by norm_num)
    (by norm_num)

/-- Matched references give 0 dB. -/
example : intensityLevel ((2:ℝ) ^ 2 / 3) (2 ^ 2 / 3) = 0 := by
  have h := intensityLevel_eq_pressureLevel (p_rms := 2) (p_ref := 2)
    (Z := 3) (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num
