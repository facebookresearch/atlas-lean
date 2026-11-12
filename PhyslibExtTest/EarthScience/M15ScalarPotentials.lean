/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.M15ScalarPotentials

/-!
# Quadratic-potential derivative checks

Concrete consumers of `PhyslibExt.EarthScience.M15ScalarPotentials`: a
numeric quadratic, its constant second derivative, and the degenerate
linear case `a = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`a = 3`, `b = 2`, `c = 5`, the potential at `x = 1` has derivative
`2*3*1 + 2 = 8` and second derivative `6`.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.M15ScalarPotentials`
-/

/-- Numeric quadratic `3*x^2 + 2*x + 5` has derivative `8` at `x = 1`. -/
example : HasDerivAt (fun x : ℝ => 3 * x ^ 2 + 2 * x + 5) 8 1 := by
  have h := EarthScience.quadratic_hasDerivAt 3 2 5 1
  norm_num at h
  exact h

/-- The same quadratic has constant second derivative `6`: its derivative
function `6*x + 2` has derivative `6` at `x = 1`. -/
example : HasDerivAt (fun x : ℝ => 6 * x + 2) 6 1 := by
  have h := EarthScience.quadratic_second_hasDerivAt 3 2 1
  norm_num at h
  exact h

/-- Degenerate case `a = 0`: the profile is linear, so the second
derivative is `0`. -/
example (b x : ℝ) : HasDerivAt (fun x : ℝ => 2 * 0 * x + b) 0 x := by
  simpa using EarthScience.quadratic_second_hasDerivAt 0 b x

/-- Degenerate case `a = 0`: the first derivative is the constant `b`. -/
example (b c x : ℝ) :
    HasDerivAt (fun x : ℝ => 0 * x ^ 2 + b * x + c) b x := by
  simpa using EarthScience.quadratic_hasDerivAt 0 b c x
