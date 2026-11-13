/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-!
# Isochrons: slope and age from coeval closed samples

For coeval closed samples with common initial daughter/stable ratio `b`,
`D_i/S_i = b + (P_i/S_i)*(exp(λ*t)-1)`; two samples with distinct parent
ratios identify the slope `exp(λ*t)-1` and the age `t = log(1+m)/λ`.

## i. Overview

`x_i = P_i/S_i` is the parent/stable ratio and `y_i = D_i/S_i` the
daughter/stable ratio of sample `i`. The two-sample slope recovers
`exp(λ*t)-1`, and the logarithm inverts it to the age. Errors-in-both-axes
inference is separate and not claimed here.

## ii. Key results

- `EarthScience.isochron_slope_eq`: the two-sample slope is `exp(λ*t)-1`.
- `EarthScience.isochron_age_eq`: the age is `log(1 + slope)/λ`.

## iii. References

- `Real.log_exp` in `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`.
-/

@[expose] public section

namespace EarthScience

/-- Isochron slope: for coeval closed samples with common initial
daughter/stable ratio `b`, `D_i/S_i = b + (P_i/S_i)*(exp(λ*t)-1)`, the
slope between two samples with distinct parent ratios is `exp(λ*t)-1`. -/
theorem isochron_slope_eq (lam t b x1 x2 y1 y2 : ℝ) (hx : x1 ≠ x2)
    (hy1 : y1 = b + x1 * (Real.exp (lam * t) - 1))
    (hy2 : y2 = b + x2 * (Real.exp (lam * t) - 1)) :
    (y2 - y1) / (x2 - x1) = Real.exp (lam * t) - 1 := by
  have hne : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hdiff : y2 - y1 = (x2 - x1) * (Real.exp (lam * t) - 1) := by
    rw [hy1, hy2]
    ring
  calc (y2 - y1) / (x2 - x1)
      = ((x2 - x1) * (Real.exp (lam * t) - 1)) / (x2 - x1) := by rw [hdiff]
    _ = Real.exp (lam * t) - 1 := by field_simp

/-- Isochron age: the slope identifies the age `t = log(1+m)/λ`. -/
theorem isochron_age_eq (lam t b x1 x2 y1 y2 : ℝ) (hlam : 0 < lam) (hx : x1 ≠ x2)
    (hy1 : y1 = b + x1 * (Real.exp (lam * t) - 1))
    (hy2 : y2 = b + x2 * (Real.exp (lam * t) - 1)) :
    Real.log (1 + (y2 - y1) / (x2 - x1)) / lam = t := by
  have hslope : (y2 - y1) / (x2 - x1) = Real.exp (lam * t) - 1 :=
    isochron_slope_eq lam t b x1 x2 y1 y2 hx hy1 hy2
  have h1 : (1 : ℝ) + (Real.exp (lam * t) - 1) = Real.exp (lam * t) := by ring
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  calc Real.log (1 + (y2 - y1) / (x2 - x1)) / lam
      = Real.log (Real.exp (lam * t)) / lam := by rw [hslope, h1]
    _ = (lam * t) / lam := by rw [Real.log_exp]
    _ = t := by field_simp

end EarthScience
