/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.S08Flexure

/-!
# Flexure checks

Concrete consumers of `PhyslibExt.EarthScience.S08Flexure`:
`D = 1`, `a = 2`, `k = 1`, `q₀ = 3` (denominator `3`), `x = 0`, plus the
zero-load and wavenumber-zero boundaries.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric flexure
- B. Boundary cases

## iv. References

- `PhyslibExt.EarthScience.S08Flexure`
-/

/-- Numeric flexure: first and fourth derivatives at `x = 0`. -/
example : HasDerivAt (fun x => (3 : ℝ) * Real.cos (1 * x) / (1 * 1 ^ 4 + 2))
    (-3 * 1 * Real.sin (1 * (0 : ℝ)) / (1 * 1 ^ 4 + 2)) 0 :=
  EarthScience.flexure_first_deriv (D := 1) (a := 2) (k := 1) (q₀ := 3) (x := 0)
    (by norm_num) (by norm_num)

/-- Numeric flexure: fourth derivative at `x = 0` is `3 * 1 / 3 = 1`. -/
example : HasDerivAt (fun x => (3 : ℝ) * 1 ^ 3 * Real.sin (1 * x) / (1 * 1 ^ 4 + 2))
    ((3 : ℝ) * 1 ^ 4 * Real.cos (1 * (0 : ℝ)) / (1 * 1 ^ 4 + 2)) 0 :=
  EarthScience.flexure_fourth_deriv (D := 1) (a := 2) (k := 1) (q₀ := 3) (x := 0)
    (by norm_num) (by norm_num)

/-- Numeric flexure equation at `x = 0`: `1 * 1 + 2 * 1 = 3`. -/
example : (1 : ℝ) * ((3 : ℝ) * 1 ^ 4 * Real.cos (1 * 0) / (1 * 1 ^ 4 + 2))
    + 2 * (3 * Real.cos (1 * (0 : ℝ)) / (1 * 1 ^ 4 + 2)) = 3 * Real.cos (1 * 0) :=
  EarthScience.flexure_equation (D := 1) (a := 2) (k := 1) (q₀ := 3) (x := 0)
    (by norm_num) (by norm_num)

/-- Zero load: the flexure equation gives `0 = 0`. -/
example : (1 : ℝ) * ((0 : ℝ) * 1 ^ 4 * Real.cos (1 * 0) / (1 * 1 ^ 4 + 2))
    + 2 * (0 * Real.cos (1 * (0 : ℝ)) / (1 * 1 ^ 4 + 2)) = 0 * Real.cos (1 * 0) :=
  EarthScience.flexure_equation (D := 1) (a := 2) (k := 1) (q₀ := 0) (x := 0)
    (by norm_num) (by norm_num)

/-- Wavenumber zero: `w = q₀ / a` is constant, `D * 0 + a * (q₀ / a) = q₀`. -/
example : (2 : ℝ) * ((3 : ℝ) / 2) = 3 := by norm_num
