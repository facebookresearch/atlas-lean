 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Latent flux and evaporation rate

## i. Overview

Latent energy flux `LE` corresponds to evaporation rate
`E = LE / (rho_w * Lv)` in water-equivalent depth/time, where `rho_w > 0`
is the water density and `Lv > 0` the latent heat of vaporization.
`LE` is in `W/m^2`, `Lv` in `J/kg`. This is a steady local unit
conversion; water availability is imposed separately by a reservoir
budget, and potential ET is distinguished from actual ET.

## ii. Key results

- `EarthScience.evaporation_rate`: `rho_w * Lv * E = LE`.
- `EarthScience.evaporation_nonneg`: `E >= 0` for `LE >= 0`.
- `EarthScience.evaporation_zero`: zero flux gives zero evaporation.
- `EarthScience.evaporation_witness`: `LE = 100, rho_w = 1000, Lv = 2.5` gives `E = 0.04`.

## iii. Table of contents

- A. Main results

## iv. References

- See the individual theorem docstrings.
-/

@[expose] public section

namespace EarthScience


/-- Latent flux to evaporation: `E = LE / (rho_w * Lv)` satisfies
`rho_w * Lv * E = LE`. -/
theorem evaporation_rate {LE ρw Lv : ℝ} (hρ : 0 < ρw) (hLv : 0 < Lv) :
    ρw * Lv * (LE / (ρw * Lv)) = LE := by
  have hne : ρw * Lv ≠ 0 := ne_of_gt (mul_pos hρ hLv)
  field_simp

/-- Evaporation is nonnegative for nonnegative latent flux. -/
theorem evaporation_nonneg {LE ρw Lv : ℝ} (hLE : 0 ≤ LE) (hρ : 0 < ρw) (hLv : 0 < Lv) :
    0 ≤ LE / (ρw * Lv) := by
  exact div_nonneg hLE (le_of_lt (mul_pos hρ hLv))

set_option linter.unusedVariables false in
/-- Zero latent flux gives zero evaporation. -/
theorem evaporation_zero {ρw Lv : ℝ} (hρ : 0 < ρw) (hLv : 0 < Lv) :
    (0 : ℝ) / (ρw * Lv) = 0 := by
  exact zero_div _

/-- Non-vacuous witness: `LE = 100, rho_w = 1000, Lv = 2.5` gives
`E = 0.04` in the corresponding units. -/
theorem evaporation_witness :
    (100 : ℝ) / (1000 * 2.5) = 0.04 := by
  norm_num



end EarthScience
