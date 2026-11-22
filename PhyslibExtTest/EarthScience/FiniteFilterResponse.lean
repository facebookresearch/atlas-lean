/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.FiniteFilterResponse

import Mathlib.Tactic.NormNum

/-!
# Finite filter frequency response checks

Concrete consumers of `PhyslibExt.EarthScience.FiniteFilterResponse`:
a generic elaboration check, the zero-frequency case where the
response is the plain sum of the taps, and the empty-filter boundary
case.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.FiniteFilterResponse`
-/

/-- Generic elaboration: the theorem applies to any taps, frequency,
and time. -/
example {n : ℕ} (h : Fin n → ℂ) (ω t : ℝ) :
    (∑ k : Fin n, h k * Complex.exp (2 * Real.pi * Complex.I * ω * (t - (k.val : ℝ))))
      = (∑ k : Fin n, h k * Complex.exp (-(2 * Real.pi * Complex.I * ω * (k.val : ℝ))))
        * Complex.exp (2 * Real.pi * Complex.I * ω * t) :=
  EarthScience.fir_frequency_response h ω t

/-- Zero frequency: with `ω = 0` every exponential is `1`, so the
filtered output is the plain tap sum `1 + 2 = 3`. -/
example : (∑ k : Fin 2, (![1, 2] : Fin 2 → ℂ) k
    * Complex.exp (2 * Real.pi * Complex.I * (0 : ℝ) * ((5 : ℝ) - (k.val : ℝ))))
    = 3 := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Empty filter boundary case: with `n = 0` both sides are `0`. -/
example (ω t : ℝ) :
    (∑ k : Fin 0, (fun _ => (1 : ℂ)) k
        * Complex.exp (2 * Real.pi * Complex.I * ω * (t - (k.val : ℝ))))
      = (∑ k : Fin 0, (fun _ => (1 : ℂ)) k
        * Complex.exp (-(2 * Real.pi * Complex.I * ω * (k.val : ℝ))))
        * Complex.exp (2 * Real.pi * Complex.I * ω * t) :=
  EarthScience.fir_frequency_response _ ω t
