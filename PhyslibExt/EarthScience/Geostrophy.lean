/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Geostrophy and ocean thermal wind

## i. Overview

For free-surface elevation with gradients `(ηx, ηy)`, f-plane balance (Coriolis parameter `f ≠ 0`,
  gravity `g`) gives the geostrophic velocities `(u, v) = (-g * ηy / f, g * ηx / f)`. The balance
  determines the velocities, and subtracting balance at two levels constrains the vertical shear
  (thermal wind) while leaving the reference velocity undetermined. The elevation gradients are
  given scalars here; no shared fluid-state framework is introduced.

## ii. Key results

- `EarthScience.geostrophic_balance`: the geostrophic velocities satisfy `f * u = -g * ηy` and `f *
  v = g * ηx`.
- `EarthScience.geostrophic_unique`: balance plus `f ≠ 0` determines the velocities.
- `EarthScience.thermal_wind_shear`: shear between two levels satisfies the differenced balance.

## iii. Table of contents

- A. Geostrophic balance
- B. Thermal-wind shear

## iv. References

- `field_simp` / `linear_combination` in Mathlib (tactics).
-/

@[expose] public section

namespace EarthScience

/-- Geostrophic balance: with `f ≠ 0`, the velocities
`u = -g * η_y / f`, `v = g * η_x / f` satisfy `f * u = -g * η_y` and
`f * v = g * η_x`, where `η_x, η_y` are the surface-elevation gradients. -/
theorem geostrophic_balance {f g ηx ηy : ℝ} (hf : f ≠ 0) :
    f * (-g * ηy / f) = -g * ηy ∧ f * (g * ηx / f) = g * ηx := by
  constructor
  · field_simp
  · field_simp

/-- Converse: balance plus `f ≠ 0` determines the geostrophic velocities. -/
theorem geostrophic_unique {f g ηx ηy u v : ℝ} (hf : f ≠ 0)
    (hu : f * u = -g * ηy) (hv : f * v = g * ηx) :
    u = -g * ηy / f ∧ v = g * ηx / f := by
  constructor
  · field_simp
    linear_combination hu
  · field_simp
    linear_combination hv

/-- Thermal-wind shear: subtracting geostrophic balance at two levels, the
vertical shear satisfies `f * (u₁ - u₀) = -g * (ηy₁ - ηy₀)` and
`f * (v₁ - v₀) = g * (ηx₁ - ηx₀)`. The shear is constrained; the absolute
(reference) velocity is not determined by this balance alone. -/
theorem thermal_wind_shear {f g ηx₀ ηy₀ ηx₁ ηy₁ u₀ v₀ u₁ v₁ : ℝ}
    (hu₀ : f * u₀ = -g * ηy₀) (hv₀ : f * v₀ = g * ηx₀)
    (hu₁ : f * u₁ = -g * ηy₁) (hv₁ : f * v₁ = g * ηx₁) :
    f * (u₁ - u₀) = -g * (ηy₁ - ηy₀) ∧
      f * (v₁ - v₀) = g * (ηx₁ - ηx₀) := by
  constructor
  · linear_combination hu₁ - hu₀
  · linear_combination hv₁ - hv₀

end EarthScience
