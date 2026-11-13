/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Finite filter frequency response

For a finite impulse response `h : Fin n → ℂ`, the response to the
complex exponential input `t ↦ exp (2π i ω t)` is that input scaled by
the frequency response `H(ω) = ∑ k, h k * exp (-2π i ω k)`.

## i. Overview

The filtered output at time `t` is `∑ k, h k * exp (2π i ω (t - k))`.
Each term splits as `exp (-2π i ω k) * exp (2π i ω t)` by
`Complex.exp_add`, and the common factor `exp (2π i ω t)` pulls out of
the finite sum. This is the eigenfunction property of complex
exponentials for finite impulse-response filters: no convergence
hypotheses are needed because the sum is finite.

## ii. Key results

- `EarthScience.fir_frequency_response`: the filtered exponential
  equals the frequency response times the exponential.

## iii. References

- `Complex.exp_add`, `Finset.sum_mul` (Mathlib).
-/

@[expose] public section

namespace EarthScience

/-- Finite filter frequency response: for a finite impulse response
`h : Fin n → ℂ`, the response to the complex exponential input
`t ↦ exp (2π i ω t)` is the input scaled by the frequency response
`H(ω) = ∑ k, h k * exp (-2π i ω k)`. -/
theorem fir_frequency_response {n : ℕ} (h : Fin n → ℂ) (ω t : ℝ) :
    (∑ k : Fin n, h k * Complex.exp (2 * Real.pi * Complex.I * ω * (t - (k.val : ℝ))))
      = (∑ k : Fin n, h k * Complex.exp (-(2 * Real.pi * Complex.I * ω * (k.val : ℝ))))
        * Complex.exp (2 * Real.pi * Complex.I * ω * t) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have harg : (2 * Real.pi * Complex.I * ω * (t - (k.val : ℝ)) : ℂ)
      = (-(2 * Real.pi * Complex.I * ω * (k.val : ℝ)) : ℂ)
        + (2 * Real.pi * Complex.I * ω * t : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  ring

end EarthScience
