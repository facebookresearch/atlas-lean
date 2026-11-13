/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PhyslibExt.EarthScience.Isochrons
import Mathlib.Tactic.NormNum

/-!
# Capstone: date a synthetic closed isotope system

## i. Overview

Synthetic dimensionless count ratios; time unit years; positive stable
denominators; common initial ratio `b`. This is a synthetic teaching
example, not a date of a real sample. Decay constant
`lam = log 2 / 10` (half-life 10 years), age `t = 10`. Two samples
have distinct parent/reference ratios `x₁ = 1`, `x₂ = 2`. Daughter /
reference ratios follow the closed-system isochron
`yᵢ = b + xᵢ * (exp (lam * t) - 1)`. Since `exp (lam * 10) = 2`,
the isochron slope is `1` and the recovered age
`log (1 + slope) / lam` is `10`. All three results are corollaries of
the general two-sample theorems `EarthScience.isochron_slope_eq` and
`EarthScience.isochron_age_eq` (`PhyslibExt.EarthScience.Isochrons`),
instantiated at these parameters; only `exp (log 2) = 2` is left.

## ii. Key results

- `EarthScience.isochron_slope_eq_one`: the isochron slope is `1`.
- `EarthScience.isochron_age_recovery`: the recovered age is `10`.
- `EarthScience.isochron_slope_at_zero_age`: at age `t = 0` the slope is `0`.

## iii. Table of contents

- A. Isochron slope, age recovery, and the zero-age boundary

## iv. References

- `EarthScience.isochron_slope_eq`, `EarthScience.isochron_age_eq` in
  `PhyslibExt.EarthScience.Isochrons`.
- `Real.exp_log`, `Real.log_pos`, `Real.exp_zero` in Mathlib.

## A. Isochron slope, age recovery, and the zero-age boundary
-/

@[expose] public section

namespace EarthScience

/-- Capstone (synthetic isochron): decay constant `lam = log 2 / 10`
(half-life 10 years), age `t = 10`, two samples with parent/reference
ratios `x₁ = 1` and `x₂ = 2`, common initial ratio `b`, and
daughter/reference ratios `yᵢ = b + xᵢ * (exp (lam * t) - 1)`.
The isochron slope `(y₂ - y₁) / (x₂ - x₁)` is `1`: `isochron_slope_eq`
gives `exp (lam * 10) - 1`, and `exp (log 2) = 2`. -/
lemma isochron_slope_eq_one {b : ℝ} :
    ((b + 2 * (Real.exp ((Real.log 2 / 10) * 10) - 1))
      - (b + 1 * (Real.exp ((Real.log 2 / 10) * 10) - 1))) / (2 - 1) = 1 := by
  rw [isochron_slope_eq (Real.log 2 / 10) 10 b 1 2
      (b + 1 * (Real.exp ((Real.log 2 / 10) * 10) - 1))
      (b + 2 * (Real.exp ((Real.log 2 / 10) * 10) - 1)) (by norm_num) rfl rfl,
    div_mul_cancel₀ _ (by norm_num : (10 : ℝ) ≠ 0), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Age recovery: `isochron_age_eq` recovers the age `10` from the sample
slope, and that slope is `1` (`isochron_slope_eq_one`), so
`log (1 + 1) / (log 2 / 10) = 10`. -/
lemma isochron_age_recovery :
    Real.log (1 + 1) / (Real.log 2 / 10) = 10 := by
  have h := isochron_age_eq (Real.log 2 / 10) 10 0 1 2
    (0 + 1 * (Real.exp ((Real.log 2 / 10) * 10) - 1))
    (0 + 2 * (Real.exp ((Real.log 2 / 10) * 10) - 1))
    (div_pos (Real.log_pos one_lt_two) (by norm_num)) (by norm_num) rfl rfl
  rwa [isochron_slope_eq_one] at h

/-- Boundary case: at age `t = 0`, `isochron_slope_eq` gives the slope
`exp (lam * 0) - 1 = 0`. -/
lemma isochron_slope_at_zero_age {b : ℝ} :
    ((b + 2 * (Real.exp ((Real.log 2 / 10) * 0) - 1))
      - (b + 1 * (Real.exp ((Real.log 2 / 10) * 0) - 1))) / (2 - 1) = 0 := by
  rw [isochron_slope_eq (Real.log 2 / 10) 0 b 1 2
      (b + 1 * (Real.exp ((Real.log 2 / 10) * 0) - 1))
      (b + 2 * (Real.exp ((Real.log 2 / 10) * 0) - 1)) (by norm_num) rfl rfl,
    mul_zero, Real.exp_zero, sub_self]

end EarthScience
