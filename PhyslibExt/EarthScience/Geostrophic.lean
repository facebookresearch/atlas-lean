/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Shared rotating-fluid balance and vorticity

For `f != 0`, `rho0 > 0`, the f-plane geostrophic balance
`f * khat x u = -grad_h p / rho0`, i.e. `f * ux = -py / rho0` and
`-f * uy = -px / rho0`, uniquely gives
`u = (-py / (rho0 * f), px / (rho0 * f))`. East / north / up
orientation; the equator `f = 0` is excluded. Balance is a
reduced-model hypothesis: no dynamics or existence is inferred.

## i. Overview

The two balance equations are solved directly for `ux` and `uy`;
uniqueness follows because two solutions satisfy the same equations.
In the southern hemisphere (`f < 0`), a positive northward pressure
gradient gives a positive eastward wind: the sign flips with `f`.

## ii. Key results

- `EarthScience.geostrophic_velocity`: geostrophic velocity formula.
- `EarthScience.geostrophic_velocity_unique`: uniqueness of the solution.
- `EarthScience.geostrophic_velocity_southern`: southern-hemisphere sign.

## iii. Table of contents

- A. Geostrophic balance inversion

## iv. References

- `field_simp` / `linear_combination` in Mathlib.
- `mul_left_cancel₀` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Geostrophic balance `f * khat x u = -grad_h p / rho0`, i.e.
`f * ux = -py / rho0` and `-f * uy = -px / rho0`, for `f ≠ 0`,
`rho0 ≠ 0` uniquely gives `u = (-py / (rho0 * f), px / (rho0 * f))`. -/
theorem geostrophic_velocity {f rho0 px py ux uy : ℝ} (hf : f ≠ 0) (hrho : rho0 ≠ 0)
    (hx : f * ux = -py / rho0) (hy : -f * uy = -px / rho0) :
    ux = -py / (rho0 * f) ∧ uy = px / (rho0 * f) := by
  have hfr : rho0 * f ≠ 0 := mul_ne_zero hrho hf
  constructor
  · field_simp
    field_simp at hx
    linear_combination hx
  · field_simp
    field_simp at hy
    linear_combination -hy

/-- Uniqueness: two velocities satisfying the same geostrophic balance
coincide. -/
theorem geostrophic_velocity_unique {f rho0 px py ux1 uy1 ux2 uy2 : ℝ}
    (hf : f ≠ 0) (hrho : rho0 ≠ 0)
    (hx1 : f * ux1 = -py / rho0) (hy1 : -f * uy1 = -px / rho0)
    (hx2 : f * ux2 = -py / rho0) (hy2 : -f * uy2 = -px / rho0) :
    ux1 = ux2 ∧ uy1 = uy2 := by
  have e1 := geostrophic_velocity hf hrho hx1 hy1
  have e2 := geostrophic_velocity hf hrho hx2 hy2
  exact ⟨e1.1.trans e2.1.symm, e1.2.trans e2.2.symm⟩

/-- Opposite hemisphere: for `f < 0`, `rho0 > 0`, a positive northward
pressure gradient `py > 0` gives a positive eastward geostrophic wind
`ux > 0` (sign flips with `f`). -/
theorem geostrophic_velocity_southern {f rho0 px py ux uy : ℝ} (hf : f < 0)
    (hrho : 0 < rho0) (hpy : 0 < py)
    (hx : f * ux = -py / rho0) (hy : -f * uy = -px / rho0) :
    0 < ux := by
  have hvel := (geostrophic_velocity (ne_of_lt hf) (ne_of_gt hrho) hx hy).1
  rw [hvel]
  exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_pos_of_neg hrho hf)

end EarthScience
