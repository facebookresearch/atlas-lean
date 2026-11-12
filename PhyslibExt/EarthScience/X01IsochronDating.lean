/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

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
`log (1 + slope) / lam` is `10`. This capstone is proved
self-contained from Mathlib primitives; it does not depend on any
sibling development.

## ii. Key results

- `EarthScience.isochron_slope_eq_one`: the isochron slope is `1`.
- `EarthScience.isochron_age_recovery`: the recovered age is `10`.
- `EarthScience.isochron_slope_at_zero_age`: at age `t = 0` the slope is `0`.

## iii. Table of contents

- A. Isochron slope, age recovery, and the zero-age boundary

## iv. References

- `Real.exp_log`, `Real.log_pos`, `Real.exp_zero` in Mathlib.

## A. Isochron slope, age recovery, and the zero-age boundary
-/

@[expose] public section

namespace EarthScience

/-- Capstone (synthetic isochron): decay constant `lam = log 2 / 10`
(half-life 10 years), age `t = 10`, two samples with parent/reference
ratios `x₁ = 1` and `x₂ = 2`, common initial ratio `b`, and
daughter/reference ratios `yᵢ = b + xᵢ * (exp (lam * t) - 1)`.
The isochron slope `(y₂ - y₁) / (x₂ - x₁)` is `1`. -/
theorem isochron_slope_eq_one {b : ℝ} :
    ((b + 2 * (Real.exp ((Real.log 2 / 10) * 10) - 1))
      - (b + 1 * (Real.exp ((Real.log 2 / 10) * 10) - 1))) / (2 - 1) = 1 := by
  have h : (Real.log 2 / 10) * 10 = Real.log 2 :=
    div_mul_cancel₀ _ (by norm_num)
  rw [h, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  field_simp
  ring

/-- Age recovery: with slope `1`, the recovered age
`log (1 + slope) / lam = log 2 / (log 2 / 10)` is `10`. -/
theorem isochron_age_recovery :
    Real.log (1 + 1) / (Real.log 2 / 10) = 10 := by
  have h : (1:ℝ) + 1 = 2 := by norm_num
  rw [h]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  field_simp

/-- Boundary case: at age `t = 0`, `exp (lam * 0) - 1 = 0`, so the
isochron slope is `0`. -/
theorem isochron_slope_at_zero_age {b : ℝ} :
    ((b + 2 * (Real.exp ((Real.log 2 / 10) * 0) - 1))
      - (b + 1 * (Real.exp ((Real.log 2 / 10) * 0) - 1))) / (2 - 1) = 0 := by
  rw [mul_zero, Real.exp_zero]
  field_simp
  ring

end EarthScience
