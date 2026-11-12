/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.DerivativeErrorBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-- Concrete non-vacuous case: `f = sin` has `|f'| = |cos| ≤ 1`; with
`x₀ = 0`, `x = 1 / 2`, `δ = 1 / 2`, the output error is
`|sin (1 / 2)| ≤ 1 / 2`. -/
example : |Real.sin (1 / 2 : ℝ) - Real.sin 0| ≤ 1 * (1 / 2 : ℝ) := by
  have h := MathlibExt.Analysis.output_error_bound_of_deriv_bound
    (f := Real.sin) (L := 1) Real.differentiable_sin
    (fun x => by simpa using Real.abs_cos_le_one x)
    (x := 1 / 2) (x₀ := 0) (δ := 1 / 2) (by norm_num)
  simpa using h

/-- Boundary case: `δ = 0` forces `x = x₀`, and the output error is `0`. -/
example : |Real.sin (1 / 3 : ℝ) - Real.sin (1 / 3 : ℝ)| ≤ 1 * (0 : ℝ) := by
  have h := MathlibExt.Analysis.output_error_bound_of_deriv_bound
    (f := Real.sin) (L := 1) Real.differentiable_sin
    (fun x => by simpa using Real.abs_cos_le_one x)
    (x := 1 / 3) (x₀ := 1 / 3) (δ := 0) (by norm_num)
  exact h

/-- Boundary case: a constant function has derivative bound `L = 0`, so
the output error is `0` for any input error. -/
example : |(fun _ : ℝ => (7 : ℝ)) 5 - (fun _ : ℝ => (7 : ℝ)) 2| ≤ 0 * (3 : ℝ) := by
  have h := MathlibExt.Analysis.output_error_bound_of_deriv_bound
    (f := fun _ : ℝ => (7 : ℝ)) (L := 0) (differentiable_const 7)
    (fun x => by simp) (x := 5) (x₀ := 2) (δ := 3) (by norm_num)
  exact h
