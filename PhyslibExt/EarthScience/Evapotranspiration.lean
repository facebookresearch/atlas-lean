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
In SI units `LE` is in `W/m^2`, `rho_w` in `kg/m^3`, `Lv` in `J/kg`, and
`E` in `m/s`; the general results hold in any consistent unit system.
This is a steady local unit conversion; water availability is imposed
separately by a reservoir budget, and potential ET is distinguished from
actual ET.

`evaporation_witness` uses scaled units: its `Lv = 2.5` is in `MJ/kg`
(`2.5 * 10^6 J/kg`), so its `E = 0.04` is in `10^-6 m/s`. The SI form
`evaporation_witness_si` gives `E = 4 * 10^-8 m/s`, about `3.5 mm/day`.

## ii. Key results

- `EarthScience.evaporation_rate`: `rho_w * Lv * E = LE`.
- `EarthScience.evaporation_nonneg`: `E >= 0` for `LE >= 0`.
- `EarthScience.evaporation_eq_zero_iff`: `E = 0` exactly when `LE = 0`.
- `EarthScience.evaporation_witness`: `LE = 100, rho_w = 1000, Lv = 2.5` gives `E = 0.04`
  (`Lv` in `MJ/kg`, `E` in `10^-6 m/s`).
- `EarthScience.evaporation_witness_si`: the same case in SI units, `E = 4 * 10^-8 m/s`.

## iii. Table of contents

- A. Main results

## iv. References

- R. G. Allen, L. S. Pereira, D. Raes and M. Smith, *Crop
  evapotranspiration: Guidelines for computing crop water requirements*,
  FAO Irrigation and Drainage Paper 56, FAO, Rome (1998), Chapter 1,
  section "Units": the latent heat of vaporization is about `2.45 MJ/kg`
  at 20 °C, so 1 mm of evaporated water corresponds to `2.45 MJ/m^2`,
  which is the conversion `E = LE / (rho_w * Lv)`; Table 1 lists the
  conversion factors.
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

/-- Evaporation vanishes exactly at zero latent flux: for `rho_w, Lv > 0`,
`LE / (rho_w * Lv) = 0` if and only if `LE = 0`. The positivity
hypotheses give the forward direction. -/
theorem evaporation_eq_zero_iff {LE ρw Lv : ℝ} (hρ : 0 < ρw) (hLv : 0 < Lv) :
    LE / (ρw * Lv) = 0 ↔ LE = 0 := by
  rw [div_eq_zero_iff]
  exact or_iff_left (mul_pos hρ hLv).ne'

/-- Witness in scaled units: `LE = 100 W/m^2`, `rho_w = 1000 kg/m^3`, and
`Lv = 2.5` in `MJ/kg` (`2.5 * 10^6 J/kg`) give `E = 0.04` in `10^-6 m/s`,
that is `4 * 10^-8 m/s` (`evaporation_witness_si`). -/
theorem evaporation_witness :
    (100 : ℝ) / (1000 * 2.5) = 0.04 := by
  norm_num

/-- The same witness in SI units: `LE = 100 W/m^2`, `rho_w = 1000 kg/m^3`,
and `Lv = 2.5 * 10^6 J/kg` give `E = 4 * 10^-8 m/s`, about `3.5 mm/day`. -/
theorem evaporation_witness_si :
    (100 : ℝ) / (1000 * (2.5 * 10 ^ 6)) = 4 / 10 ^ 8 := by
  norm_num



end EarthScience
