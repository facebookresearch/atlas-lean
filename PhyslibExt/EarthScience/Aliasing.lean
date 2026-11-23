/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Geophysical time series: aliasing of uniform samples

Uniform samples of `exp(2π i f n dt)` coincide for `f` and
`f + k / dt`, `k` integer, `dt ≠ 0`. The same holds for the sampled
sine and cosine pairs.

## i. Overview

The exponent difference between the two frequencies is
`2π i * (k * n)`, an integer multiple of `2π i`, so the complex
exponential is unchanged (`Complex.exp_int_mul_two_pi_mul_I`); the
sine and cosine versions use the `2π`-periodicity lemmas
`Real.sin_add_int_mul_two_pi` / `Real.cos_add_int_mul_two_pi`.
`f` is in cycles/time, `dt` in time, `n` the integer sample index;
normalization is explicit in the exponent. This proves aliasing, not
a general sampling reconstruction theorem.

## ii. Key results

- `EarthScience.uniform_samples_aliasing`: complex samples coincide.
- `EarthScience.uniform_samples_aliasing_sin`: sampled sines coincide.
- `EarthScience.uniform_samples_aliasing_cos`: sampled cosines coincide.

## iii. Table of contents

- A. Complex samples
- B. Sine and cosine pairs

## iv. References

- `Complex.exp_int_mul_two_pi_mul_I`, `Real.sin_add_int_mul_two_pi`,
  `Real.cos_add_int_mul_two_pi` (Mathlib).

## A. Complex samples
-/

@[expose] public section

namespace EarthScience

/-- Aliasing of uniform complex samples: for `dt ≠ 0` and integer `k`,
the samples `exp(2π i f n dt)` coincide for `f` and `f + k / dt`.
This proves aliasing, not a general sampling reconstruction theorem. -/
theorem uniform_samples_aliasing {f : ℝ} {k n : ℤ} {dt : ℝ} (hdt : dt ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (f + (k : ℝ) / dt) * (n : ℝ) * dt)
      = Complex.exp (2 * Real.pi * Complex.I * f * (n : ℝ) * dt) := by
  have hdtC : (dt : ℂ) ≠ 0 := by exact_mod_cast hdt
  have hexp : (2 * Real.pi * Complex.I * (f + (k : ℝ) / dt) * (n : ℝ) * dt : ℂ)
      = (2 * Real.pi * Complex.I * f * (n : ℝ) * dt : ℂ)
        + ((k * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## B. Sine and cosine pairs -/

/-- Aliased sine pair: the sampled sines coincide for `f` and
`f + k / dt`. -/
theorem uniform_samples_aliasing_sin {f : ℝ} {k n : ℤ} {dt : ℝ} (hdt : dt ≠ 0) :
    Real.sin (2 * Real.pi * (f + (k : ℝ) / dt) * (n : ℝ) * dt)
      = Real.sin (2 * Real.pi * f * (n : ℝ) * dt) := by
  have hangle : (2 * Real.pi * (f + (k : ℝ) / dt) * (n : ℝ) * dt : ℝ)
      = (2 * Real.pi * f * (n : ℝ) * dt : ℝ)
        + ((k * n : ℤ) : ℝ) * (2 * Real.pi) := by
    field_simp
    push_cast
    ring
  rw [hangle]
  exact Real.sin_add_int_mul_two_pi _ _

/-- Aliased cosine pair: the sampled cosines coincide for `f` and
`f + k / dt`. -/
theorem uniform_samples_aliasing_cos {f : ℝ} {k n : ℤ} {dt : ℝ} (hdt : dt ≠ 0) :
    Real.cos (2 * Real.pi * (f + (k : ℝ) / dt) * (n : ℝ) * dt)
      = Real.cos (2 * Real.pi * f * (n : ℝ) * dt) := by
  have hangle : (2 * Real.pi * (f + (k : ℝ) / dt) * (n : ℝ) * dt : ℝ)
      = (2 * Real.pi * f * (n : ℝ) * dt : ℝ)
        + ((k * n : ℤ) : ℝ) * (2 * Real.pi) := by
    field_simp
    push_cast
    ring
  rw [hangle]
  exact Real.cos_add_int_mul_two_pi _ _

end EarthScience
