 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.Buoyancy

/-!
# Integral buoyancy checks

Concrete consumers of `PhyslibExt.EarthScience.Buoyancy`:
`rho = 500, g = 10, A = 3, h = 2` (force `30000`), neutral buoyancy
at half-submersion, and the emerge case `h = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.Buoyancy`
-/

/-- Numeric buoyancy: `rho = 500, g = 10, A = 3, h = 2` gives force `30000`. -/
example : ((0:ℝ) + 500 * 10 * 2) * 3 - 0 * 3 = 30000 := by norm_num

/-- Buoyancy theorem at the numeric values. -/
example : ((0:ℝ) + 500 * 10 * 2) * 3 - 0 * 3 = 500 * 10 * 3 * 2 :=
  EarthScience.buoyancy_force

/-- Pressure difference: `rho = 500, g = 10, h = 2` gives `10000`. -/
example : ((0:ℝ) + 500 * 10 * 2) - 0 = 10000 := by norm_num

/-- Neutral buoyancy: `rho = 1000, rho_b = 500, A = 2, H = 4` balances at `h = 2`. -/
example : (500:ℝ) * (2 * 4) * 10 = 1000 * 10 * 2 * ((500 / 1000) * 4) :=
  EarthScience.neutral_buoyancy (by norm_num)

/-- Emerge: `h = 0` gives zero buoyancy force. -/
example : ((0:ℝ) + 1000 * 10 * 0) * 2 - 0 * 2 = 0 := by norm_num

