/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# First-order decay and its integrated consumption

For `k` and initial concentration `c0`, `c(t) = c0 * exp(-k*t)` solves
`c' = -k*c`, starts at `c0`, and its integrated consumption over `[0, t]`
is `c0 - c(t)`.

## i. Overview

Closed, well-mixed, constant-volume first-order reaction with initial
concentration `c0`. No transport-limited or reversible claim is made, and
the source of a fitted `k` is empirical metadata, outside this file.

## ii. Key results

- `EarthScience.firstOrder_decay_hasDerivAt`: `c(t) = c0*exp(-k*t)`
  satisfies `c' = -k*c`.
- `EarthScience.firstOrder_decay_initial`: `c(0) = c0`.
- `EarthScience.firstOrder_decay_consumption`: `∫ s in 0..t, k*c(s) = c0 - c(t)`.

## iii. References

- `Real.hasDerivAt_exp` in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean`.
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` for the consumption integral.
-/

@[expose] public section

namespace EarthScience

/-- First-order decay: `c(t) = c0 * exp(-k*t)` solves `c' = -k*c`. -/
theorem firstOrder_decay_hasDerivAt (k c0 t : ℝ) :
    HasDerivAt (fun t => c0 * Real.exp (-k * t))
      (-k * (c0 * Real.exp (-k * t))) t := by
  have h := (((hasDerivAt_id t).const_mul (-k)).exp.const_mul c0)
  simp only [id_eq, mul_one] at h
  convert h using 1
  ring

/-- First-order decay starts at `c0`. -/
theorem firstOrder_decay_initial (k c0 : ℝ) :
    c0 * Real.exp (-k * 0) = c0 := by
  simp

/-- Integrated consumption of first-order decay over `[0, t]` is `c0 - c(t)`. -/
theorem firstOrder_decay_consumption (k c0 t : ℝ) :
    ∫ s in (0 : ℝ)..t, k * (c0 * Real.exp (-k * s)) =
      c0 - c0 * Real.exp (-k * t) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s => -(c0 * Real.exp (-k * s))) (k * (c0 * Real.exp (-k * x))) x := by
    intro x _
    have hg := firstOrder_decay_hasDerivAt k c0 x
    have hn := hg.neg
    convert hn using 1
    ring
  have hcont : Continuous (fun s : ℝ => k * (c0 * Real.exp (-k * s))) := by
    continuity
  have hint : IntervalIntegrable (fun s : ℝ => k * (c0 * Real.exp (-k * s)))
      MeasureTheory.volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [sub_eq_add_neg, add_comm] using hFTC

end EarthScience
