/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Flexure: periodic solution of the linear flexure equation

For `D * w'''' + a * w = q₀ * cos (k * x)`, `w = q₀ * cos (k * x) / (D * k ^ 4 + a)`
solves the infinite/periodic linear flexure model.

## i. Overview

`D ≥ 0` is the flexural rigidity, `a > 0` the restoring coefficient
(`a = (ρm - ρ_fill) * g` in the isostatic setting), `k` the wavenumber,
`q₀` the load amplitude, `w` the deflection. The four derivatives of the
cosine profile are computed explicitly, and the flexure equation follows
because `D * k ^ 4 + a ≠ 0`. Small deflection; no finite-domain edge
conditions are claimed. Wavenumber zero is a separate case (then
`w = q₀ / a` is constant and the equation holds trivially).

## ii. Key results

- `EarthScience.flexure_first_deriv`, `flexure_second_deriv`,
  `flexure_third_deriv`, `flexure_fourth_deriv`: the four derivatives.
- `EarthScience.flexure_equation`: `D * w'''' + a * w = q₀ * cos (k * x)`.

## iii. Table of contents

- A. Derivatives of the flexure profile
- B. Flexure equation

## iv. References

- `Real.hasDerivAt_cos`, `Real.hasDerivAt_sin` in Mathlib.

## A. Derivatives of the flexure profile
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Flexure: first derivative of `w(x) = q₀ * cos (k * x) / (D * k ^ 4 + a)`. -/
theorem flexure_first_deriv {D a k q₀ x : ℝ} (hD : 0 ≤ D) (ha : 0 < a) :
    HasDerivAt (fun x => q₀ * Real.cos (k * x) / (D * k ^ 4 + a))
      (-q₀ * k * Real.sin (k * x) / (D * k ^ 4 + a)) x := by
  have h1 : HasDerivAt (fun x : ℝ => k * x) k x := by
    simpa using (hasDerivAt_id' x).const_mul k
  have h2 : HasDerivAt Real.cos (-Real.sin (k * x)) (k * x) := Real.hasDerivAt_cos (k * x)
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (k * x)) (-Real.sin (k * x) * k) x :=
    h2.comp x h1
  have h4 := h3.const_mul q₀
  have h5 := h4.div_const (D * k ^ 4 + a)
  convert h5 using 1
  ring

set_option linter.unusedVariables false in
/-- Flexure: second derivative. -/
theorem flexure_second_deriv {D a k q₀ x : ℝ} (hD : 0 ≤ D) (ha : 0 < a) :
    HasDerivAt (fun x => -q₀ * k * Real.sin (k * x) / (D * k ^ 4 + a))
      (-q₀ * k ^ 2 * Real.cos (k * x) / (D * k ^ 4 + a)) x := by
  have h1 : HasDerivAt (fun x : ℝ => k * x) k x := by
    simpa using (hasDerivAt_id' x).const_mul k
  have h2 : HasDerivAt Real.sin (Real.cos (k * x)) (k * x) := Real.hasDerivAt_sin (k * x)
  have h3 : HasDerivAt (fun x : ℝ => Real.sin (k * x)) (Real.cos (k * x) * k) x :=
    h2.comp x h1
  have h4 := h3.const_mul (-q₀ * k)
  have h5 := h4.div_const (D * k ^ 4 + a)
  convert h5 using 1
  ring

set_option linter.unusedVariables false in
/-- Flexure: third derivative. -/
theorem flexure_third_deriv {D a k q₀ x : ℝ} (hD : 0 ≤ D) (ha : 0 < a) :
    HasDerivAt (fun x => -q₀ * k ^ 2 * Real.cos (k * x) / (D * k ^ 4 + a))
      (q₀ * k ^ 3 * Real.sin (k * x) / (D * k ^ 4 + a)) x := by
  have h1 : HasDerivAt (fun x : ℝ => k * x) k x := by
    simpa using (hasDerivAt_id' x).const_mul k
  have h2 : HasDerivAt Real.cos (-Real.sin (k * x)) (k * x) := Real.hasDerivAt_cos (k * x)
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (k * x)) (-Real.sin (k * x) * k) x :=
    h2.comp x h1
  have h4 := h3.const_mul (-q₀ * k ^ 2)
  have h5 := h4.div_const (D * k ^ 4 + a)
  convert h5 using 1
  ring

set_option linter.unusedVariables false in
/-- Flexure: fourth derivative. -/
theorem flexure_fourth_deriv {D a k q₀ x : ℝ} (hD : 0 ≤ D) (ha : 0 < a) :
    HasDerivAt (fun x => q₀ * k ^ 3 * Real.sin (k * x) / (D * k ^ 4 + a))
      (q₀ * k ^ 4 * Real.cos (k * x) / (D * k ^ 4 + a)) x := by
  have h1 : HasDerivAt (fun x : ℝ => k * x) k x := by
    simpa using (hasDerivAt_id' x).const_mul k
  have h2 : HasDerivAt Real.sin (Real.cos (k * x)) (k * x) := Real.hasDerivAt_sin (k * x)
  have h3 : HasDerivAt (fun x : ℝ => Real.sin (k * x)) (Real.cos (k * x) * k) x :=
    h2.comp x h1
  have h4 := h3.const_mul (q₀ * k ^ 3)
  have h5 := h4.div_const (D * k ^ 4 + a)
  convert h5 using 1
  ring

/-! ## B. Flexure equation -/

/-- Flexure equation: `D * w'''' + a * w = q₀ * cos (k * x)`. -/
theorem flexure_equation {D a k q₀ x : ℝ} (hD : 0 ≤ D) (ha : 0 < a) :
    D * (q₀ * k ^ 4 * Real.cos (k * x) / (D * k ^ 4 + a)) +
        a * (q₀ * Real.cos (k * x) / (D * k ^ 4 + a)) = q₀ * Real.cos (k * x) := by
  have hc : D * k ^ 4 + a ≠ 0 := by
    have hpos : 0 < D * k ^ 4 + a := by positivity
    exact ne_of_gt hpos
  field_simp

end EarthScience
