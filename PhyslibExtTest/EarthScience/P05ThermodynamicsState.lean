/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.P05ThermodynamicsState

/-!
# Isochoric heating checks

Concrete consumers of `PhyslibExt.EarthScience.P05ThermodynamicsState`:
`C = 2`, `Q = 6` (so `ΔT = 3`), heating from `T0 = 300` to `303`, and
the zero-input boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric heating
- B. Zero-input boundary

## iv. References

- `PhyslibExt.EarthScience.P05ThermodynamicsState`
-/

/-- Numeric heating: `U1 - U0 = 6`, `C * ΔT = 2 * 3`, so `ΔT = 3`. -/
example : (303 : ℝ) - 300 = 6 / 2 :=
  EarthScience.isochoric_temperature_change (C := 2) (Q := 6) (U0 := 5) (U1 := 11)
    (T0 := 300) (T1 := 303) (by norm_num) (by norm_num) (by norm_num)

/-- Numeric heating via the internal-energy function. -/
example : ((5 : ℝ) + 2 * (((300 : ℝ) + 6 / 2) - 300)) - 5 = 6 ∧
    ((300 : ℝ) + 6 / 2) - 300 = 6 / 2 :=
  EarthScience.isochoric_heating (C := 2) (Q := 6) (U0 := 5) (T0 := 300) (by norm_num)

/-- Zero-input boundary: no energy change, no temperature change. -/
example : (300 : ℝ) = 300 :=
  EarthScience.isochoric_zero_heating (C := 2) (U0 := 5) (U1 := 5) (T0 := 300) (T1 := 300)
    (by norm_num) (by norm_num) (by norm_num)

/-- Cooling boundary: negative `Q` lowers the temperature. -/
example : ((300 : ℝ) + (-4) / 2) - 300 = (-4) / 2 :=
  (EarthScience.isochoric_heating (C := 2) (Q := -4) (U0 := 5) (T0 := 300)
    (by norm_num)).2
