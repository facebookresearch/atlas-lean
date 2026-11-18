/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Geotechnical.PhaseRelations
import Mathlib.Tactic.FieldSimp

/-!
# Gravimetric and volumetric water-content relation

## i. Overview

For a soil element with solid volume `Vs`, void volume `Vv`, water
volume `Vw`, solid density `ρs`, and water density `ρw`: the degree
of saturation `S = Vw / Vv`, void ratio `e = Vv / Vs`, gravimetric
water content `w_g = Mw / Ms` (water mass over solid mass), and
specific gravity `G_s = ρs / ρw` satisfy `S * e = w_g * G_s`,
with masses `Mw = ρw * Vw` and `Ms = ρs * Vs`.

## ii. Key results

- `EarthScience.saturation_mul_voidRatio`: the phase relation
  `S * e = w_g * G_s`.

## iii. Table of contents

- A. Water-content phase relation

## iv. References

- R. F. Craig, *Craig's Soil Mechanics*, 8th edition, Spon
  Press, 2012 (soil phase relations).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Water-content phase relation -/

/-- Degree of saturation: water volume over void volume. -/
noncomputable def degreeOfSaturation (Vw Vv : ℝ) : ℝ := Vw / Vv

/-- Gravimetric water content: water mass over solid mass. -/
noncomputable def gravimetricWaterContent (Mw Ms : ℝ) : ℝ := Mw / Ms

/-- Specific gravity of solids: solid density over water density. -/
noncomputable def specificGravity (ρs ρw : ℝ) : ℝ := ρs / ρw

/-- The phase relation `S * e = w_g * G_s`. -/
theorem saturation_mul_voidRatio {Vs Vv Vw ρs ρw : ℝ}
    (hVs : 0 < Vs) (hVv : 0 < Vv) (hρs : 0 < ρs) (hρw : 0 < ρw) :
    degreeOfSaturation Vw Vv * voidRatio Vs Vv
      = gravimetricWaterContent (ρw * Vw) (ρs * Vs)
        * specificGravity ρs ρw := by
  unfold degreeOfSaturation voidRatio gravimetricWaterContent specificGravity
  have hVs' : Vs ≠ 0 := ne_of_gt hVs
  have hVv' : Vv ≠ 0 := ne_of_gt hVv
  have hρs' : ρs ≠ 0 := ne_of_gt hρs
  have hρw' : ρw ≠ 0 := ne_of_gt hρw
  have hρsVs : ρs * Vs ≠ 0 := mul_ne_zero hρs' hVs'
  field_simp

/-- On the physical domain `0 ≤ Vw ≤ Vv` with `0 < Vv`, the degree
of saturation lies in `[0, 1]`. Outside that domain
`degreeOfSaturation` is the same totalized quotient, and
`saturation_mul_voidRatio` is the corresponding algebraic
identity for arbitrary real `Vw`. -/
lemma degreeOfSaturation_mem_Icc {Vw Vv : ℝ} (h0 : 0 ≤ Vw)
    (hle : Vw ≤ Vv) (hVv : 0 < Vv) :
    degreeOfSaturation Vw Vv ∈ Set.Icc 0 1 := by
  constructor
  · exact div_nonneg h0 hVv.le
  · exact div_le_one_of_le₀ hle hVv.le

end EarthScience
