/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.ArrheniusLaw

/-!
# Arrhenius law checks

Concrete consumers of `PhyslibExt.EarthScience.ArrheniusLaw`: with
`A = 1`, `Ea = 1000`, `R = 8.314`, the rate at `400 K` exceeds the rate
at `300 K`, and the rate at `300 K` is positive.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.ArrheniusLaw`
-/

/-- `k(300) < k(400)` for `A = 1`, `Ea = 1000`, `R = 8.314`. -/
example :
    (1 : ℝ) * Real.exp (-1000 / (8.314 * 300)) <
      (1 : ℝ) * Real.exp (-1000 / (8.314 * 400)) := by
  have h := EarthScience.arrhenius_strictMonoOn (A := (1 : ℝ)) (Ea := 1000) (R := 8.314)
    (by norm_num) (by norm_num) (by norm_num)
  exact h (by norm_num) (by norm_num) (by norm_num)

/-- `k(300) > 0` for the same parameters. -/
example :
    0 < (1 : ℝ) * Real.exp (-1000 / (8.314 * 300)) :=
  EarthScience.arrhenius_pos (A := (1 : ℝ)) (hA := by norm_num) (hT := by norm_num)

/-- Boundary case: at any `T > 0` the rate is positive, e.g. `T = 1`. -/
example :
    0 < (2 : ℝ) * Real.exp (-500 / (10 * 1)) :=
  EarthScience.arrhenius_pos (A := (2 : ℝ)) (hA := by norm_num) (hT := by norm_num)
