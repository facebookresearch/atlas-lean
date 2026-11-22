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
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FinCases

/-!
# Rotating frames and Coriolis force

For constant angular velocity `Ω` in `ℝ³`, the Coriolis acceleration
`2 Ω × v` is perpendicular to the velocity `v`, so a rotating frame does
no work through the Coriolis term. Differentiating `Ω × r(t)` for
constant `Ω` gives `Ω × r'(t)`, the transport law that the rotating
acceleration terms are derived from.

## i. Overview

The cross product is Mathlib's `crossProduct`, written `Ω ⨯₃ v`, with
`Ω ⨯₃ v = (Ω₁v₂ - Ω₂v₁, Ω₂v₀ - Ω₀v₂, Ω₀v₁ - Ω₁v₀)` (`cross_apply`). The
dot product `v ⬝ᵥ (2 • (Ω ⨯₃ v))` vanishes because `v ⬝ᵥ (Ω ⨯₃ v) = 0`
(`dot_cross_self`). The transport law is proved componentwise. Variable `Ω`
would need a separate Euler-acceleration term and is not treated here.

## ii. Key results

- `EarthScience.dot_coriolis_eq_zero`: `v ⬝ᵥ (2 • (Ω ⨯₃ v)) = 0`.
- `EarthScience.hasDerivAt_cross_const`: the derivative of `Ω ⨯₃ r t` is
  `Ω ⨯₃ r'`.

## iii. Table of contents

- A. Coriolis perpendicularity and transport

## iv. References

- `crossProduct`, `cross_apply` and `dot_cross_self` in
  `Mathlib/LinearAlgebra/CrossProduct.lean` (Mathlib).
- `hasDerivAt_pi` in `Mathlib/Analysis/Calculus/Deriv/Prod.lean`
  (Mathlib).

## A. Coriolis perpendicularity and transport
-/

@[expose] public section

namespace EarthScience

open Matrix

/-- The Coriolis acceleration `2 Ω × v` is perpendicular to the velocity `v`:
`v ⬝ᵥ (2 • (Ω ⨯₃ v)) = 0`. -/
theorem dot_coriolis_eq_zero (Ω v : Fin 3 → ℝ) :
    v ⬝ᵥ (2 • (Ω ⨯₃ v)) = 0 := by
  rw [dotProduct_smul, dot_cross_self, smul_zero]

/-- Transport of a cross product with constant `Ω`: differentiating
`Ω ⨯₃ r t` gives `Ω ⨯₃ r'`, where `r'` is the componentwise derivative of `r`
at `t`. -/
theorem hasDerivAt_cross_const (Ω : Fin 3 → ℝ) (r : ℝ → Fin 3 → ℝ)
    (r' : Fin 3 → ℝ) (t : ℝ)
    (h : ∀ i, HasDerivAt (fun t => r t i) (r' i) t) :
    HasDerivAt (fun t => Ω ⨯₃ r t) (Ω ⨯₃ r') t := by
  simp only [cross_apply]
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

end EarthScience
