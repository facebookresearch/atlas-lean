/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.S12ConvectionScaling

/-!
# Convection-scaling checks

Concrete consumers of `PhyslibExt.EarthScience.S12ConvectionScaling`:
unit parameters give `Ra = 10`, and the zero-buoyancy boundary gives
`Ra = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric Rayleigh number
- B. Zero-buoyancy boundary

## iv. References

- `PhyslibExt.EarthScience.S12ConvectionScaling`
-/

/-- Numeric Rayleigh number: `g = 10`, all other parameters `1`, gives `Ra = 10`. -/
example : (10 : ℝ) * 1 * 1 * 1 ^ 3 / (1 * 1) = 10 := by norm_num

/-- The factorisation at unit parameters: `(10 / 1) * (1 / 1) = 10`. -/
example : ((10 : ℝ) * 1 * 1 * 1 / 1) * (1 ^ 2 / 1)
    = 10 * 1 * 1 * 1 ^ 3 / (1 * 1) :=
  EarthScience.rayleigh_number_factorisation (g := 10) (α := 1) (ΔT := 1) (H := 1)
    (ν := 1) (κ := 1) (by norm_num) (by norm_num)

/-- Positivity at unit parameters. -/
example : 0 < (10 : ℝ) * 1 * 1 * 1 ^ 3 / (1 * 1) :=
  EarthScience.rayleigh_number_pos (g := 10) (α := 1) (ΔT := 1) (H := 1)
    (ν := 1) (κ := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- Zero-buoyancy boundary: `ΔT = 0` gives `Ra = 0`. -/
example : (10 : ℝ) * 1 * 0 * 1 ^ 3 / (1 * 1) = 0 :=
  EarthScience.rayleigh_number_zero_buoyancy (g := 10) (α := 1) (H := 1)
    (ν := 1) (κ := 1) (by norm_num) (by norm_num)
