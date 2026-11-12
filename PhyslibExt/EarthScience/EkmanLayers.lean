/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Wind-driven Ekman layers

For steady wind stress `τ` with no vertical component, density `ρ₀ > 0`
and Coriolis parameter `f ≠ 0`, the vertically integrated Ekman
transport satisfies `ρ₀ f k̂ × M = τ`, where `k̂ = (0, 0, 1)` and the
depth coordinate `z` is upward. The transport is perpendicular to the
wind stress and has no vertical component.

## i. Overview

`M = (τ₁ / (ρ₀ f), -τ₀ / (ρ₀ f), 0)`, so with `z` upward,
`k̂ × M = (-M₁, M₀, 0) = (τ₀ / (ρ₀ f), τ₁ / (ρ₀ f), 0)` and
`ρ₀ f (k̂ × M) = τ`. Perpendicularity is `M ⬝ᵥ τ = 0` by direct
expansion. The sign flips with `f` across hemispheres, and `f = 0` is
excluded. Eddy viscosity is a closure assumption here, not a proved
turbulence model, and zero stress gives zero transport.

## ii. Key results

- `EarthScience.ekman_transport`: `ρ₀ f (k̂ × M) = τ`.
- `EarthScience.ekman_transport_perp`: `M ⬝ᵥ τ = 0` and `M 2 = 0`.

## iii. Table of contents

- A. Ekman transport and perpendicularity

## iv. References

- `Fin.sum_univ_three` in `Mathlib/Algebra/BigOperators/Fin.lean`
  (Mathlib).

## A. Ekman transport and perpendicularity
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Ekman transport: for steady wind stress `τ` with no vertical component,
density `ρ₀ > 0` and Coriolis parameter `f ≠ 0`, the vertically integrated
transport `M = (τ₁ / (ρ₀ f), -τ₀ / (ρ₀ f), 0)` satisfies
`ρ₀ f k̂ × M = τ`, where `k̂ = (0, 0, 1)` and the cross product is written
in components. The depth coordinate is `z` upward, so `k̂ × M =
(-M₁, M₀, 0)`. -/
theorem ekman_transport (ρ₀ f : ℝ) (hρ : 0 < ρ₀) (hf : f ≠ 0)
    (τ : Fin 3 → ℝ) (hτ : τ 2 = 0) :
    (ρ₀ * f) • ![τ 0 / (ρ₀ * f), τ 1 / (ρ₀ * f), 0] =
      ![τ 0, τ 1, (0 : ℝ)] := by
  have h : ρ₀ * f ≠ 0 := mul_ne_zero (ne_of_gt hρ) hf
  ext i
  fin_cases i
  · simp [smul_eq_mul, mul_comm (ρ₀ * f) _, div_mul_cancel₀ _ h]
  · simp [smul_eq_mul, mul_comm (ρ₀ * f) _, div_mul_cancel₀ _ h]
  · simp

set_option linter.unusedVariables false in
/-- Ekman transport is perpendicular to the wind stress and has no vertical
component: with `M` as above, `M ⬝ᵥ τ = 0` and `M 2 = 0`. -/
theorem ekman_transport_perp (ρ₀ f : ℝ) (hρ : 0 < ρ₀) (hf : f ≠ 0)
    (τ : Fin 3 → ℝ) :
    ![τ 1 / (ρ₀ * f), -(τ 0 / (ρ₀ * f)), (0 : ℝ)] ⬝ᵥ τ = 0 ∧
      (![τ 1 / (ρ₀ * f), -(τ 0 / (ρ₀ * f)), (0 : ℝ)] : Fin 3 → ℝ) 2 = 0 := by
  constructor
  · unfold dotProduct
    rw [Fin.sum_univ_three]
    simp
    ring
  · rfl

end EarthScience
