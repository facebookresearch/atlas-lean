/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.InstrumentBiasBound

import Mathlib.Tactic.NormNum

/-!
# Instrument bias bound checks

Concrete consumers of `PhyslibExt.EarthScience.InstrumentBiasBound`:
a non-vacuous interior case, the boundary case where the bias attains
its cap, and a negative-slope case.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.InstrumentBiasBound`
-/

/-- Interior case: `a = 2, b = 3, x = 5, ε = 0.4, B = 0.5` gives
error `0.2 ≤ 0.25`. -/
example : |((2 * 5 + 3 + (0.4 : ℝ) - 3) / 2) - 5| ≤ (0.5 : ℝ) / |2| :=
  EarthScience.instrument_bias_output_bound (a := (2 : ℝ)) (b := (3 : ℝ))
    (x := (5 : ℝ)) (ε := (0.4 : ℝ)) (B := (0.5 : ℝ)) (by norm_num)
    (by norm_num)

/-- Boundary arithmetic: with bias attaining its cap, `ε = B = 0.5`,
`a = 2`, the signed estimator error is exactly `B / |a| = 0.25`. -/
example : ((2 * 5 + 3 + (0.5 : ℝ) - 3) / 2) - 5 = (0.5 : ℝ) / |2| := by
  norm_num

/-- Boundary case via the theorem: bias attaining its cap gives
error `≤ B / |a|`. -/
example : |((2 * 5 + 3 + (0.5 : ℝ) - 3) / 2) - 5| ≤ (0.5 : ℝ) / |2| :=
  EarthScience.instrument_bias_output_bound (a := (2 : ℝ)) (b := (3 : ℝ))
    (x := (5 : ℝ)) (ε := (0.5 : ℝ)) (B := (0.5 : ℝ)) (by norm_num)
    (by norm_num)

/-- Negative slope: `a = -2, ε = -0.5, B = 0.5` gives error
`0.25 ≤ 0.25`. -/
example : |((-2 * 5 + 3 + (-0.5 : ℝ) - 3) / -2) - 5| ≤ (0.5 : ℝ) / |-2| :=
  EarthScience.instrument_bias_output_bound (a := (-2 : ℝ)) (b := (3 : ℝ))
    (x := (5 : ℝ)) (ε := (-0.5 : ℝ)) (B := (0.5 : ℝ)) (by norm_num)
    (by norm_num)
