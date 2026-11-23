/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.GibbsEnergyDifferential

/-!
# Gibbs energy differential checks

Concrete consumers of
`PhyslibExt.EarthScience.GibbsEnergyDifferential`: the numeric
instance `T = 300`, `dS = 2`, `p = 1`, `dV = 3`, `S = 5`, `dT = 10`,
`V = 2`, `dp = 4`, giving `dU = 597` and `dG = -42`, and the boundary
`dT = dp = 0`, giving `dG = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.GibbsEnergyDifferential`
-/

/-- Numeric instance: `dG = -42`. -/
example : (-42 : ℝ) = -(5 : ℝ) * 10 + 2 * 4 := by
  have h := EarthScience.gibbs_energy_differential (dU := 597) (dS := 2) (dV := 3)
    (dT := 10) (dp := 4) (dG := (-42 : ℝ)) (T := 300) (p := 1) (S := 5) (V := 2)
    (by norm_num) (by norm_num)
  exact h

/-- Boundary case: `dT = dp = 0` gives `dG = 0`. -/
example : (0 : ℝ) = -(5 : ℝ) * 0 + 2 * 0 := by
  have h := EarthScience.gibbs_energy_differential (dU := 597) (dS := 2) (dV := 3)
    (dT := 0) (dp := 0) (dG := (0 : ℝ)) (T := 300) (p := 1) (S := 5) (V := 2)
    (by norm_num) (by norm_num)
  exact h
