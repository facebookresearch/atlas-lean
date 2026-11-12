/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.FirstOrderPropagationRemainder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-- The second derivative of `Real.sin` is `-Real.sin`, hence bounded by
`1` everywhere. -/
private theorem deriv_deriv_sin (x : ℝ) : deriv (deriv Real.sin) x = -Real.sin x := by
  rw [Real.deriv_sin, Real.deriv_cos]

/-- Concrete non-vacuous case: `f = Real.sin`, `x₀ = 0`, `h = 1 / 2`,
`M = 1`. The remainder `|sin (1 / 2) - 1 / 2|` is positive and at most
`1 / 8`. -/
example : |Real.sin (0 + 1 / 2 : ℝ) - Real.sin 0 - deriv Real.sin 0 * (1 / 2 : ℝ)|
    ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ 2 := by
  have h := MathlibExt.Analysis.first_order_propagation_remainder_bound
    (f := Real.sin) (M := 1) Real.contDiff_sin
    (fun x => by rw [deriv_deriv_sin, abs_neg]; exact Real.abs_sin_le_one x)
    (x₀ := 0) (h := 1 / 2)
  simpa using h

/-- Boundary case `h = 0`: the remainder is `0` and the bound is `0`. -/
example : |Real.sin (0 + 0 : ℝ) - Real.sin 0 - deriv Real.sin 0 * (0 : ℝ)|
    ≤ (1 / 2 : ℝ) * (0 : ℝ) ^ 2 := by
  have h := MathlibExt.Analysis.first_order_propagation_remainder_bound
    (f := Real.sin) (M := 1) Real.contDiff_sin
    (fun x => by rw [deriv_deriv_sin, abs_neg]; exact Real.abs_sin_le_one x)
    (x₀ := 0) (h := 0)
  exact h

/-- Boundary case: a linear function has `f'' = 0`, so with `M = 0` the
remainder is exactly `0` for every `h`. -/
example : |(fun x : ℝ => 3 * x + 1) (2 + 5) - (fun x : ℝ => 3 * x + 1) 2
    - deriv (fun x : ℝ => 3 * x + 1) 2 * 5| ≤ (0 / 2) * (5 : ℝ) ^ 2 := by
  have hderiv1 : ∀ y : ℝ, deriv (fun x : ℝ => 3 * x + 1) y = 3 := by
    intro y
    have h := ((hasDerivAt_id' y).const_mul 3 |>.add_const 1).deriv
    rw [mul_one] at h
    exact h
  have h := MathlibExt.Analysis.first_order_propagation_remainder_bound
    (f := fun x : ℝ => 3 * x + 1) (M := 0) (by fun_prop)
    (fun x => by
      have hfun : deriv (fun x : ℝ => 3 * x + 1) = fun _ => (3 : ℝ) :=
        funext hderiv1
      rw [hfun]
      simp)
    (x₀ := 2) (h := 5)
  simpa using h
