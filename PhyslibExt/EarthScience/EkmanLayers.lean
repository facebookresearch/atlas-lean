/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Wind-driven Ekman layers

For steady wind stress `τ` with no vertical component, density `ρ₀ > 0`
and Coriolis parameter `f ≠ 0`, the vertically integrated Ekman
transport `M` satisfies `ρ₀ f k̂ × M = τ`, where `k̂ = (0, 0, 1)`, `×` is
Mathlib's cross product `⨯₃`, and the depth coordinate `z` is upward.
The transport is perpendicular to the wind stress and has no vertical
component.

## i. Overview

`ekmanTransport ρ₀ f τ = M = (τ₁ / (ρ₀ f), -τ₀ / (ρ₀ f), 0)`. With `z`
upward, `cross_apply` gives `k̂ ⨯₃ M = (-M₁, M₀, 0) = (τ₀ / (ρ₀ f), τ₁ / (ρ₀ f), 0)`,
so `(ρ₀ f) • (k̂ ⨯₃ M) = τ`, the third component by `τ 2 = 0`.
Perpendicularity is `M ⬝ᵥ τ = 0` by direct expansion. For `f > 0`
(northern hemisphere) the transport points to the right of the wind
stress; the sign flips with `f` across hemispheres, and `f = 0` is
excluded. Eddy viscosity is a closure assumption here, not a proved
turbulence model, and zero stress gives zero transport.

## ii. Key results

- `EarthScience.ekmanTransport`: the transport `M`.
- `EarthScience.ekman_transport`: `(ρ₀ f) • (k̂ ⨯₃ M) = τ`.
- `EarthScience.ekman_transport_perp`: `M ⬝ᵥ τ = 0` and `M 2 = 0`.

## iii. Table of contents

- A. Ekman transport and perpendicularity

## iv. References

- V. W. Ekman, *On the influence of the earth's rotation on
  ocean-currents*, Arkiv för Matematik, Astronomi och Fysik 2 (11)
  (1905), 1–52: the original derivation that the net wind-driven
  transport of the surface layer is at right angles to the wind, to the
  right of it in the northern hemisphere.
- B. Cushman-Roisin and J.-M. Beckers, *Introduction to Geophysical
  Fluid Dynamics: Physical and Numerical Aspects*, 2nd ed., Academic
  Press (2011), Chapter 8 (The Ekman layer): the surface Ekman layer,
  with `z` upward and `f > 0` in the northern hemisphere, whose
  vertically integrated volume transport is
  `(τʸ / (ρ₀ f), -τˣ / (ρ₀ f))`.
- `cross_apply` in `Mathlib/LinearAlgebra/CrossProduct.lean` and
  `Fin.sum_univ_three` in `Mathlib/Algebra/BigOperators/Fin.lean`
  (Mathlib).

## A. Ekman transport and perpendicularity
-/

@[expose] public section

namespace EarthScience

open Matrix

/-- The vertically integrated Ekman transport
`M = (τ₁ / (ρ₀ f), -τ₀ / (ρ₀ f), 0)` driven by the wind stress `τ`, for
density `ρ₀` and Coriolis parameter `f`. -/
noncomputable def ekmanTransport (ρ₀ f : ℝ) (τ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![τ 1 / (ρ₀ * f), -(τ 0 / (ρ₀ * f)), 0]

/-- Ekman transport: for steady wind stress `τ` with no vertical component,
density `ρ₀ > 0` and Coriolis parameter `f ≠ 0`, the vertically integrated
transport `M = ekmanTransport ρ₀ f τ` satisfies `ρ₀ f k̂ × M = τ`, where
`k̂ = (0, 0, 1)` and `×` is Mathlib's cross product `⨯₃`. The depth
coordinate is `z` upward. -/
theorem ekman_transport (ρ₀ f : ℝ) (hρ : 0 < ρ₀) (hf : f ≠ 0)
    (τ : Fin 3 → ℝ) (hτ : τ 2 = 0) :
    (ρ₀ * f) • ((![0, 0, 1] : Fin 3 → ℝ) ⨯₃ ekmanTransport ρ₀ f τ) = τ := by
  have h : ρ₀ * f ≠ 0 := mul_ne_zero (ne_of_gt hρ) hf
  ext i
  fin_cases i
  · simp [ekmanTransport, cross_apply, mul_div_cancel₀ _ h]
  · simp [ekmanTransport, cross_apply, mul_div_cancel₀ _ h]
  · simp [ekmanTransport, cross_apply, hτ]

set_option linter.unusedVariables false in
/-- Ekman transport is perpendicular to the wind stress and has no vertical
component: `M ⬝ᵥ τ = 0` and `M 2 = 0` for `M = ekmanTransport ρ₀ f τ`. -/
theorem ekman_transport_perp (ρ₀ f : ℝ) (hρ : 0 < ρ₀) (hf : f ≠ 0)
    (τ : Fin 3 → ℝ) :
    ekmanTransport ρ₀ f τ ⬝ᵥ τ = 0 ∧ ekmanTransport ρ₀ f τ 2 = 0 := by
  constructor
  · unfold ekmanTransport dotProduct
    rw [Fin.sum_univ_three]
    simp
    ring
  · rfl

end EarthScience
