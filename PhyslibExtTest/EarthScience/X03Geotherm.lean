/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.X03Geotherm

/-!
# Geotherm capstone checks

Concrete consumers of `PhyslibExt.EarthScience.X03Geotherm`:
gradient magnitude at the stated flux, the linear profile at
`T₀ = 300` (`T(1000) = 280`, derivative `-(2 / 100)`, flux `6 / 100`),
and the constant-gradient boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Gradient magnitude and linear profile

## iv. References

- `PhyslibExt.EarthScience.X03Geotherm`
-/

/-- Gradient magnitude at the stated flux: `|grad| = 0.02`. -/
example : |-(2 / 100 : ℝ)| = 2 / 100 :=
  EarthScience.fourier_gradient_magnitude (grad := -(2 / 100)) (by norm_num)

/-- Linear profile at `T₀ = 300`: `T(1000) = 280`. -/
example : (300 : ℝ) - (2 / 100) * 1000 = 280 := by norm_num

/-- Linear profile derivative and flux at `T₀ = 300, z = 1000`. -/
example : HasDerivAt (fun z => (300 : ℝ) - (2 / 100 : ℝ) * z) (-(2 / 100 : ℝ)) 1000 ∧
    -(3 : ℝ) * (-(2 / 100 : ℝ)) = 6 / 100 :=
  EarthScience.geotherm_linear_profile_flux (T₀ := 300) (z := 1000)

/-- Constant gradient at `T₀ = 300`: derivative is `-(2 / 100)` everywhere. -/
example (z : ℝ) : deriv (fun z => (300 : ℝ) - (2 / 100 : ℝ) * z) z = -(2 / 100 : ℝ) :=
  EarthScience.geotherm_second_derivative_zero (T₀ := 300) z
