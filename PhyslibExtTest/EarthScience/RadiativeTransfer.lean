/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.RadiativeTransfer

/-!
# Beer–Lambert checks

Concrete consumers of `PhyslibExt.EarthScience.RadiativeTransfer`:
`I0 = 2, κ = 1` (so `I(0) = 2`, `I(1) = 2 * exp(-1)`, `I'(0) = -2`),
the no-absorption case `κ = 0`, and the zero-source case `I0 = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric ray `I0 = 2, κ = 1`
- B. No-absorption and zero-source boundaries

## iv. References

- `PhyslibExt.EarthScience.RadiativeTransfer`
-/

/-- Numeric ray initial value: `I(0) = 2`. -/
example : (2 : ℝ) * Real.exp (-(1 : ℝ) * 0) = 2 :=
  EarthScience.beer_lambert_initial

/-- Numeric ray at `s = 1`: `I(1) = 2 * exp(-1)`. -/
example : (2 : ℝ) * Real.exp (-(1 : ℝ) * 1) = 2 * Real.exp (-1) := by
  norm_num

/-- Numeric ray ODE at `s = 0`: `I'(0) = -2`. -/
example :
    HasDerivAt (fun s => (2 : ℝ) * Real.exp (-(1 : ℝ) * s))
      (-(1 : ℝ) * ((2 : ℝ) * Real.exp (-(1 : ℝ) * 0))) 0 :=
  EarthScience.beer_lambert_hasDerivAt 0

/-- Numeric ray nonnegativity: `I(3) >= 0`. -/
example : 0 ≤ (2 : ℝ) * Real.exp (-(1 : ℝ) * 3) :=
  EarthScience.beer_lambert_nonneg (by norm_num) 3

/-- No absorption: `κ = 0` keeps `I = 2` at `s = 5`. -/
example : (2 : ℝ) * Real.exp (-(0 : ℝ) * 5) = 2 :=
  EarthScience.beer_lambert_no_absorption 5

/-- Zero source: `I0 = 0` gives `I = 0` everywhere. -/
example (s : ℝ) : (0 : ℝ) * Real.exp (-(1 : ℝ) * s) = 0 := by simp
