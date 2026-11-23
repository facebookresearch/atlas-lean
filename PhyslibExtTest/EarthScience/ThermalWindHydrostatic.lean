/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.ThermalWindHydrostatic

/-!
# Thermal wind from hydrostatic balance: checks

Concrete consumers of `PhyslibExt.EarthScience.ThermalWindHydrostatic`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With `f = 2`, `g = 10`, `ρ₀ = 5`,
density `ρ = 5 - x - y` and hydrostatic pressure `p = -10 (5 - x - y) z`, the geostrophic
velocity is `(u, v) = (-z, z)`. Every hypothesis of `thermal_wind_of_hydrostatic` holds, and the
theorem gives the nonzero shear `∂u/∂z = -1`, `∂v/∂z = 1` from `∂ρ/∂x = ∂ρ/∂y = -1`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Public shape
- B. Concrete sheared geostrophic flow

## iv. References

- `PhyslibExt.EarthScience.ThermalWindHydrostatic`
-/

open Space

/-!
## A. Public shape
-/

/-- Public shape of `thermal_wind_of_hydrostatic`. -/
example {f g ρ₀ : ℝ} {p ρ u v : Space 3 → ℝ} (hf : f ≠ 0) (hρ₀ : ρ₀ ≠ 0)
    (hp : ContDiff ℝ 2 p) (hhydro : ∀ x, ∂[2] p x = -ρ x * g)
    (hu : ∀ x, f * u x = -∂[1] p x / ρ₀) (hv : ∀ x, f * v x = ∂[0] p x / ρ₀) (x : Space 3) :
    f * ∂[2] u x = g / ρ₀ * ∂[1] ρ x ∧ f * ∂[2] v x = -(g / ρ₀) * ∂[0] ρ x :=
  EarthScience.thermal_wind_of_hydrostatic hf hρ₀ hp hhydro hu hv x

/-!
## B. Concrete sheared geostrophic flow
-/

/-- Concrete sheared flow: `f = 2`, `g = 10`, `ρ₀ = 5`, `ρ = 5 - x - y`,
`p = -10 (5 - x - y) z` and `(u, v) = (-z, z)` satisfy hydrostatic and geostrophic balance,
and `thermal_wind_of_hydrostatic` turns `∂ρ/∂x = ∂ρ/∂y = -1` into the shear `∂u/∂z = -1`,
`∂v/∂z = 1`. -/
example (x : Space 3) :
    ∂[2] (fun y : Space 3 => -y 2) x = -1 ∧ ∂[2] (fun y : Space 3 => y 2) x = 1 := by
  -- Product rule for the pressure.
  have hp (i : Fin 3) (y : Space 3) :
      ∂[i] (fun y : Space 3 => -10 * (5 - y 0 - y 1) * y 2) y =
        -10 * ((5 - y 0 - y 1) * ∂[i] (fun y : Space 3 => y 2) y -
          (∂[i] (fun y : Space 3 => y 0) y + ∂[i] (fun y : Space 3 => y 1) y) * y 2) := by
    rw [Space.deriv_eq]
    simp (disch := fun_prop) only [fderiv_fun_mul, fderiv_fun_sub, fderiv_fun_const]
    simp [← Space.deriv_eq]
    ring
  -- The horizontal density gradient is `(-1, -1)`.
  have hρ : ∂[0] (fun y : Space 3 => 5 - y 0 - y 1) x = -1 ∧
      ∂[1] (fun y : Space 3 => 5 - y 0 - y 1) x = -1 := by
    constructor <;>
    · rw [Space.deriv_eq]
      simp (disch := fun_prop) only [fderiv_fun_sub, fderiv_fun_const]
      simp [← Space.deriv_eq, Space.deriv_component]
  obtain ⟨hu, hv⟩ := EarthScience.thermal_wind_of_hydrostatic (f := 2) (g := 10) (ρ₀ := 5)
    (p := fun y => -10 * (5 - y 0 - y 1) * y 2) (ρ := fun y => 5 - y 0 - y 1)
    (u := fun y => -y 2) (v := fun y => y 2) (by norm_num) (by norm_num) (by fun_prop)
    (fun y => by rw [hp]; simp [Space.deriv_component]; ring)
    (fun y => by rw [hp]; simp [Space.deriv_component]; ring)
    (fun y => by rw [hp]; simp [Space.deriv_component]; ring) x
  rw [hρ.2] at hu
  rw [hρ.1] at hv
  constructor <;> linarith
