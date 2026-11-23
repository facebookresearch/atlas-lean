/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Joukowsky traveling-wave jump

## i. Overview

For the water-hammer traveling-wave states `h = F(x ∓ a t)`,
`q = ±(gA/a) F(x ∓ a t)`, with pressure `p = rho g h` and velocity
`v = q / A`, the jump relations `Δp = ± rho a Δv` hold between any
two states at the same time.

## ii. Key results

- `FluidDynamics.TravelingWave.jump_right`: `Δp = rho a Δv`.
- `FluidDynamics.TravelingWave.jump_left`: `Δp = -rho a Δv`.

## iii. Table of contents

- A. Traveling waves

## iv. References

- N. Joukowsky (1898); E. B. Wylie and V. L. Streeter, *Fluid
  Transients in Systems*, Prentice Hall, 1993.

## A. Traveling waves
-/

@[expose] public section

namespace FluidDynamics.TravelingWave

/-- Right-traveling water-hammer state from a profile `F`:
`h(t,x) = F (x - a t)`, `q(t,x) = (gA/a) F (x - a t)`. -/
noncomputable def hR (a : ℝ) (F : ℝ → ℝ) (t x : ℝ) : ℝ := F (x - a * t)

/-- Right-traveling discharge. -/
noncomputable def qR (g A a : ℝ) (F : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (g * A / a) * F (x - a * t)

/-- Left-traveling water-hammer state: `h(t,x) = F (x + a t)`. -/
noncomputable def hL (a : ℝ) (F : ℝ → ℝ) (t x : ℝ) : ℝ := F (x + a * t)

/-- Left-traveling discharge. -/
noncomputable def qL (g A a : ℝ) (F : ℝ → ℝ) (t x : ℝ) : ℝ :=
  -(g * A / a) * F (x + a * t)

/-- Right-traveling waves satisfy `q = (gA/a) h` pointwise. -/
theorem qR_eq {g A a : ℝ} (F : ℝ → ℝ) (t x : ℝ) :
    qR g A a F t x = (g * A / a) * hR a F t x := by
  rfl

/-- Joukowsky relation, right-traveling: with pressure
`p = rho * g * h` and velocity `v = q / A`,
`Δp = rho * a * Δv` between any two states at the same time. -/
theorem jump_right {rho g A a : ℝ} (ha : a ≠ 0) (hA : A ≠ 0) (F : ℝ → ℝ) (t x₁ x₂ : ℝ) :
    rho * g * (hR a F t x₂ - hR a F t x₁)
      = rho * a * ((qR g A a F t x₂ - qR g A a F t x₁) / A) := by
  unfold hR qR
  field_simp

/-- Joukowsky relation, left-traveling: `Δp = - rho * a * Δv`. -/
theorem jump_left {rho g A a : ℝ} (ha : a ≠ 0) (hA : A ≠ 0) (F : ℝ → ℝ) (t x₁ x₂ : ℝ) :
    rho * g * (hL a F t x₂ - hL a F t x₁)
      = - rho * a * ((qL g A a F t x₂ - qL g A a F t x₁) / A) := by
  unfold hL qL
  field_simp
  ring

end FluidDynamics.TravelingWave
