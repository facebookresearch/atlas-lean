/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Soil phase relations: void ratio and porosity

## i. Overview

A soil element of solid volume `Vs > 0` and void volume `Vv ≥ 0` (both in
the same volume unit) has void ratio `e = Vv / Vs` and porosity
`n = Vv / (Vs + Vv)`, the void fraction of the total volume. This module
records the normalization between the two coordinates and the range of the
porosity. Saturation splits of the voids and any effective-stress law are
separate models, not treated here.

## ii. Key results

- `EarthScience.voidRatio`, `EarthScience.porosity`: the two phase
  coordinates.
- `EarthScience.porosity_eq_voidRatio_div_one_add_voidRatio`: `n = e / (1 + e)`.
- `EarthScience.porosity_nonneg`, `EarthScience.porosity_lt_one`: `0 ≤ n < 1`.

## iii. Table of contents

- A. Phase coordinates and their normalization

## iv. References

- B. M. Das and K. Sobhan, *Principles of Geotechnical Engineering*,
  10th edition, Cengage, 2022, Chapter 3 (Weight–Volume Relationships):
  void ratio `e = Vv / Vs`, porosity `n = Vv / (Vs + Vv)`, and the derived
  relation `n = e / (1 + e)`.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Phase coordinates and their normalization -/

/-- Void ratio of a soil (or other two-phase solid/void) element:
`e = Vv / Vs`, the void volume `Vv` divided by the solid volume `Vs`, both
in the same volume unit, so `e` is dimensionless. Physically meaningful
for `0 < Vs` and `0 ≤ Vv`; outside that range this is the same real
formula by total division. -/
noncomputable def voidRatio (Vs Vv : ℝ) : ℝ :=
  Vv / Vs

/-- Porosity of a soil (or other two-phase solid/void) element:
`n = Vv / (Vs + Vv)`, the void fraction of the total volume `Vs + Vv`,
with both volumes in the same unit, so `n` is dimensionless. Physically
meaningful for `0 < Vs` and `0 ≤ Vv`; outside that range this is the same
real formula by total division. -/
noncomputable def porosity (Vs Vv : ℝ) : ℝ :=
  Vv / (Vs + Vv)

/-- Porosity is the normalized void ratio: `n = e / (1 + e)`. -/
theorem porosity_eq_voidRatio_div_one_add_voidRatio {Vs Vv : ℝ}
    (hVs : 0 < Vs) (hVv : 0 ≤ Vv) :
    porosity Vs Vv = voidRatio Vs Vv / (1 + voidRatio Vs Vv) := by
  unfold porosity voidRatio
  have hVs' : Vs ≠ 0 := ne_of_gt hVs
  have hsum : Vs + Vv ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hVs hVv)
  have he : (0 : ℝ) ≤ Vv / Vs := div_nonneg hVv (le_of_lt hVs)
  have hpos : (0 : ℝ) < 1 + Vv / Vs := add_pos_of_pos_of_nonneg zero_lt_one he
  have hden : (1 : ℝ) + Vv / Vs ≠ 0 := ne_of_gt hpos
  field_simp

/-- Porosity is nonnegative. -/
theorem porosity_nonneg {Vs Vv : ℝ} (hVs : 0 < Vs) (hVv : 0 ≤ Vv) :
    0 ≤ porosity Vs Vv := by
  unfold porosity
  exact div_nonneg hVv (le_of_lt (add_pos_of_pos_of_nonneg hVs hVv))

/-- Porosity is strictly below one: the solid volume is positive, so voids
never exhaust the total volume. -/
theorem porosity_lt_one {Vs Vv : ℝ} (hVs : 0 < Vs) (hVv : 0 ≤ Vv) :
    porosity Vs Vv < 1 := by
  unfold porosity
  have hsum : 0 < Vs + Vv := add_pos_of_pos_of_nonneg hVs hVv
  exact (div_lt_one hsum).mpr (by linarith)

end EarthScience
