/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.PorousEnergyPorts
import Mathlib.Tactic.FieldSimp

/-!
# Radial Darcy profile checks

Concrete consumers of `PhyslibExt.EarthScience.PorousEnergyPorts`: on the annulus
`1 ≤ r ≤ exp 1` with head `0` at the well, signed injection and extraction move the head at
`r = exp 1` to `-1` and `1`, and with a negative transmissivity injection raises it to `1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Signed discharge and negative transmissivity

## iv. References

- `PhyslibExt.EarthScience.PorousEnergyPorts`
-/

open EarthScience

/-! ## A. Signed discharge and negative transmissivity -/

/-- Signed injection and extraction on the annulus `1 ≤ r ≤ exp 1` with `Tr = 1` and head `0`
at the well: the injection `Q = 2 π` gives head `-1` at `r = exp 1`, and the extraction
`Q = -2 π` gives head `1`. -/
example :
    radialDarcyHead 0 (2 * Real.pi) 1 1 (Real.exp 1) = -1 ∧
      radialDarcyHead 0 (-(2 * Real.pi)) 1 1 (Real.exp 1) = 1 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  constructor
  · unfold radialDarcyHead
    simp only [div_one, Real.log_exp, mul_one, zero_sub]
    field_simp
  · unfold radialDarcyHead
    simp only [div_one, Real.log_exp, mul_one, zero_sub]
    field_simp

/-- Negative-transmissivity fixture: with `Tr = -1`, head `0` at the well radius `1` and the
injection `Q = 2 π`, the profile rises to `1` at `r = exp 1`, toward the outward discharge. -/
example :
    radialDarcyHead 0 (2 * Real.pi) (-1) 1 (Real.exp 1) = 1 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold radialDarcyHead
  simp only [div_one, Real.log_exp, mul_one, zero_sub]
  field_simp
