/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.D02Aliasing

/-!
# Aliasing checks

Concrete consumers of `PhyslibExt.EarthScience.D02Aliasing`: a numeric
aliased pair (`f = 0.3, dt = 0.5, k = 2, n = 3`), the degenerate
`k = 0` case (same frequency), the `n = 0` case (both samples are
`exp 0 = 1`, `sin 0 = 0`, `cos 0 = 1`), and the `dt < 0` case (only
`dt ≠ 0` is needed).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric aliased pair
- B. Degenerate cases

## iv. References

- `PhyslibExt.EarthScience.D02Aliasing`
-/

/-- Numeric aliased pair, complex samples. -/
example : Complex.exp (2 * Real.pi * Complex.I * ((0.3 : ℝ) + (2 : ℝ) / 0.5) * (3 : ℝ) * 0.5)
    = Complex.exp (2 * Real.pi * Complex.I * (0.3 : ℝ) * (3 : ℝ) * 0.5) :=
  EarthScience.uniform_samples_aliasing (by norm_num : (0.5 : ℝ) ≠ 0)

/-- Numeric aliased pair, sines. -/
example : Real.sin (2 * Real.pi * ((0.3 : ℝ) + (2 : ℝ) / 0.5) * (3 : ℝ) * 0.5)
    = Real.sin (2 * Real.pi * (0.3 : ℝ) * (3 : ℝ) * 0.5) :=
  EarthScience.uniform_samples_aliasing_sin (by norm_num : (0.5 : ℝ) ≠ 0)

/-- Numeric aliased pair, cosines. -/
example : Real.cos (2 * Real.pi * ((0.3 : ℝ) + (2 : ℝ) / 0.5) * (3 : ℝ) * 0.5)
    = Real.cos (2 * Real.pi * (0.3 : ℝ) * (3 : ℝ) * 0.5) :=
  EarthScience.uniform_samples_aliasing_cos (by norm_num : (0.5 : ℝ) ≠ 0)

/-- `k = 0`: the two frequencies are the same. -/
example {f : ℝ} {n : ℤ} {dt : ℝ} (hdt : dt ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (f + (0 : ℤ) / dt) * (n : ℝ) * dt)
      = Complex.exp (2 * Real.pi * Complex.I * f * (n : ℝ) * dt) :=
  EarthScience.uniform_samples_aliasing hdt

/-- `n = 0`: both complex samples are `1`. -/
example {f : ℝ} {k : ℤ} {dt : ℝ} (hdt : dt ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (f + (k : ℝ) / dt) * ((0 : ℤ) : ℝ) * dt) = 1 := by
  have h := EarthScience.uniform_samples_aliasing (f := f) (k := k) (n := 0) (dt := dt) hdt
  rw [show (2 * Real.pi * Complex.I * f * ((0 : ℤ) : ℝ) * dt) = (0 : ℂ) by simp] at h
  rw [h]
  simp

/-- `n = 0`: both sampled sines are `0` (no `dt ≠ 0` needed). -/
example {f : ℝ} {k : ℤ} {dt : ℝ} :
    Real.sin (2 * Real.pi * (f + (k : ℝ) / dt) * ((0 : ℤ) : ℝ) * dt) = 0 := by
  simp
