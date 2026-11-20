/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

/-!
# Dimensional analysis: nondimensionalizing advection-diffusion

With `x = L * x̂`, `t = (L / U) * t̂`, `c = C0 * ĉ`, the
advection-diffusion equation `c_t + U * c_x = D * c_xx` becomes
`ĉ_t̂ + ĉ_x̂ = (1 / Pe) * ĉ_x̂x̂` with Péclet number `Pe = U * L / D`.

## i. Overview

The chain rule gives the derivative-value relations
`c_t = C0 * (U / L) * ĉ_t̂`, `c_x = (C0 / L) * ĉ_x̂`,
`c_xx = (C0 / L²) * ĉ_x̂x̂` at corresponding points. These relations
are hypotheses of the main theorem, not proved here; the theorem is
the scaling algebra that turns them plus the PDE into the
nondimensional equation. This is not a general Buckingham-Pi existence
theorem. All characteristic scales are positive; zero scales are
excluded. `U * L / D` is dimensionless.

## ii. Key results

- `EarthScience.advection_diffusion_nondimensional`: the scaled
  equation `ĉ_t̂ + ĉ_x̂ = (1 / Pe) * ĉ_x̂x̂`.
- `EarthScience.peclet_pos`: `Pe > 0` and `1 / Pe = D / (U * L)`.
- `EarthScience.peclet_example`: a concrete Péclet witness.

## iii. Table of contents

- A. Nondimensional equation
- B. Péclet number
- C. Concrete witness

## iv. References

- `field_simp`, `linear_combination`, `div_pos`, `one_div_div`
  (Mathlib).

## A. Nondimensional equation
-/

@[expose] public section

namespace EarthScience

/-- Nondimensionalization of the advection-diffusion equation: with
`x = L * x̂`, `t = (L / U) * t̂`, `c = C0 * ĉ`, the chain rule gives
`c_t = C0 * (U / L) * ĉ_t̂`, `c_x = (C0 / L) * ĉ_x̂`,
`c_xx = (C0 / L ^ 2) * ĉ_x̂x̂` (as derivative values at corresponding
points). If `c` satisfies `c_t + U * c_x = D * c_xx`, then the scaled
derivatives satisfy `ĉ_t̂ + ĉ_x̂ = (1 / Pe) * ĉ_x̂x̂` with
`Pe = U * L / D`. -/
theorem advection_diffusion_nondimensional {L U D C0 : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hD : 0 < D) (hC0 : 0 < C0)
    {ct cx cxx chat chatx chatxx : ℝ}
    (hct : ct = C0 * (U / L) * chat) (hcx : cx = (C0 / L) * chatx)
    (hcxx : cxx = (C0 / L ^ 2) * chatxx)
    (hPDE : ct + U * cx = D * cxx) :
    chat + chatx = (1 / (U * L / D)) * chatxx := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hU' : U ≠ 0 := ne_of_gt hU
  have hD' : D ≠ 0 := ne_of_gt hD
  have hC0' : C0 ≠ 0 := ne_of_gt hC0
  have hUL : U * L ≠ 0 := mul_ne_zero hU' hL'
  have hfac : C0 * U / L ≠ 0 := div_ne_zero (mul_ne_zero hC0' hU') hL'
  rw [hct, hcx, hcxx] at hPDE
  have hfact : (C0 * U / L) * (chat + chatx) = D * (C0 / L ^ 2) * chatxx := by
    linear_combination hPDE
  rw [one_div_div]
  have hmul : (C0 * U / L) * (chat + chatx)
      = (C0 * U / L) * ((D / (U * L)) * chatxx) := by
    rw [hfact]
    field_simp
  exact mul_left_cancel₀ hfac hmul

/-! ## B. Péclet number -/

/-- The Péclet number is positive and its reciprocal is `D / (U * L)`. -/
theorem peclet_pos {L U D : ℝ} (hL : 0 < L) (hU : 0 < U) (hD : 0 < D) :
    0 < U * L / D ∧ 1 / (U * L / D) = D / (U * L) := by
  refine ⟨div_pos (mul_pos hU hL) hD, ?_⟩
  rw [one_div_div]

/-! ## C. Concrete witness -/

/-- Concrete Péclet witness: `L = 2, U = 3, D = 1` gives `Pe = 6`, and
scaled derivative values `ĉ_t̂ = 1, ĉ_x̂ = 2, ĉ_x̂x̂ = 18` satisfy
`1 + 2 = (1 / 6) * 18`. -/
theorem peclet_example : (1 : ℝ) + 2 = (1 / (3 * 2 / 1)) * 18 := by
  norm_num

end EarthScience
