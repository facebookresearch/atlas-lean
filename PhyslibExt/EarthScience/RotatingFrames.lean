/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Rotating frames and Coriolis force

For constant angular velocity `Ω` in `ℝ³`, the Coriolis acceleration
`2 Ω × v` is perpendicular to the velocity `v`, so a rotating frame does
no work through the Coriolis term. Differentiating `Ω × r(t)` for
constant `Ω` gives `Ω × r'(t)`, the transport law that the rotating
acceleration terms are derived from. The f-plane Coriolis parameter is
`f = 2 Ω sin φ`.

## i. Overview

The cross product is written in components,
`Ω × v = (Ω₁v₂ - Ω₂v₁, Ω₂v₀ - Ω₀v₂, Ω₀v₁ - Ω₁v₀)`. The dot product
`v ⬝ᵥ (2 Ω × v)` vanishes by direct expansion. The transport law is
proved componentwise. The f-plane parameter vanishes at the equator,
is odd in latitude, and equals `2 Ω` at the pole. Variable `Ω` would
need a separate Euler-acceleration term and is not treated here.

## ii. Key results

- `EarthScience.dot_coriolis_eq_zero`: `v ⬝ᵥ (2 Ω × v) = 0`.
- `EarthScience.hasDerivAt_cross_const`: the derivative of `Ω × r(t)` is
  `Ω × r'(t)`.
- `EarthScience.coriolis_parameter_values`: f-plane values at the
  equator, under sign flip, and at the pole.

## iii. Table of contents

- A. Coriolis perpendicularity, transport, and the f-plane

## iv. References

- `hasDerivAt_pi` in `Mathlib/Analysis/Calculus/Deriv/Prod.lean`
  (Mathlib).

## A. Coriolis perpendicularity, transport, and the f-plane
-/

@[expose] public section

namespace EarthScience

/-- The Coriolis acceleration `2 Ω × v` is perpendicular to the velocity `v`:
`v ⬝ᵥ (2 Ω × v) = 0`. The cross product is written in components,
`Ω × v = (Ω₁v₂ - Ω₂v₁, Ω₂v₀ - Ω₀v₂, Ω₀v₁ - Ω₁v₀)`. -/
theorem dot_coriolis_eq_zero (Ω v : Fin 3 → ℝ) :
    v ⬝ᵥ (2 • ![Ω 1 * v 2 - Ω 2 * v 1, Ω 2 * v 0 - Ω 0 * v 2,
      Ω 0 * v 1 - Ω 1 * v 0]) = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Transport of a cross product with constant `Ω`: differentiating
`Ω × r t` componentwise gives `Ω × r'`, where `r'` is the componentwise
derivative of `r` at `t`. -/
theorem hasDerivAt_cross_const (Ω : Fin 3 → ℝ) (r : ℝ → Fin 3 → ℝ)
    (r' : Fin 3 → ℝ) (t : ℝ)
    (h : ∀ i, HasDerivAt (fun t => r t i) (r' i) t) :
    HasDerivAt (fun t => ![Ω 1 * r t 2 - Ω 2 * r t 1, Ω 2 * r t 0 - Ω 0 * r t 2,
      Ω 0 * r t 1 - Ω 1 * r t 0])
      ![Ω 1 * r' 2 - Ω 2 * r' 1, Ω 2 * r' 0 - Ω 0 * r' 2,
        Ω 0 * r' 1 - Ω 1 * r' 0] t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simp only []
    exact HasDerivAt.sub (HasDerivAt.const_mul (Ω 1) (h 2))
      (HasDerivAt.const_mul (Ω 2) (h 1))
  · simp only []
    exact HasDerivAt.sub (HasDerivAt.const_mul (Ω 2) (h 0))
      (HasDerivAt.const_mul (Ω 0) (h 2))
  · simp only []
    exact HasDerivAt.sub (HasDerivAt.const_mul (Ω 0) (h 1))
      (HasDerivAt.const_mul (Ω 1) (h 0))

/-- The f-plane Coriolis parameter `f = 2 Ω sin φ` vanishes at the equator
and is odd in latitude. -/
theorem coriolis_parameter_values (Ω φ : ℝ) :
    2 * Ω * Real.sin 0 = 0 ∧
      2 * Ω * Real.sin (-φ) = -(2 * Ω * Real.sin φ) ∧
      2 * Ω * Real.sin (Real.pi / 2) = 2 * Ω := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · rw [Real.sin_neg]; ring
  · rw [Real.sin_pi_div_two]; ring

end EarthScience
