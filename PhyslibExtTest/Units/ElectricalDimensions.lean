/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Units.ElectricalDimensions

/-!
# Tests for `PhyslibExt.Units.ElectricalDimensions`

* the headline identities and the ISQ bridge, used as a public API;
* the SI exponents of volt, ohm, farad and henry at all seven ISQ base quantities;
* Ohm's law, `P = V I`, the `R C` and `L / R` time constants and `Q = I t` at concrete values in
  `SI` and in `SIPrimed` coordinates (length, time, mass, charge and temperature units scaled by
  `2`, `3`, `5`, `7` and `11`), and the coordinate of `chargeOfCurrent`;
* the two dimensionally wrong laws `P = V + I` and `f = R C` are rejected.
-/

@[expose] public section

namespace PhyslibExtTest.Units.ElectricalDimensions

open Dimension LTMCTUnitChoices UnitDependent _root_.Units.ElectricalDimensions

/-! ## A. Headline identities and the ISQ bridge -/

example : voltageDim * currentDim = powerDim :=
  electricalDimensions_correct.1

example : resistanceDim * capacitanceDim = T𝓭 ∧ inductanceDim / resistanceDim = T𝓭 :=
  ⟨electricalDimensions_correct.2.1, electricalDimensions_correct.2.2.1⟩

example : toISQHom C𝓭 = toISQHom currentDim * toISQHom T𝓭 :=
  electricalDimensions_correct.2.2.2.2.2.2.2

example : toISQHom C𝓭 = single ISQDimensionBase.current * single ISQDimensionBase.time :=
  toISQHom_charge_eq_single_current_mul_single_time

-- R C is a time, not a frequency, and voltage is not current.
example : resistanceDim * capacitanceDim ≠ T𝓭⁻¹ := resistanceDim_mul_capacitanceDim_ne_inv_time
example : voltageDim ≠ currentDim := voltageDim_ne_currentDim

/-! ## B. SI exponents of volt, ohm, farad and henry -/

-- Volt = kg m² s⁻³ A⁻¹.
example :
    (toISQHom voltageDim).exponent .length = 2 ∧ (toISQHom voltageDim).exponent .mass = 1 ∧
      (toISQHom voltageDim).exponent .time = -3 ∧
      (toISQHom voltageDim).exponent .current = -1 ∧
      (toISQHom voltageDim).exponent .temperature = 0 ∧
      (toISQHom voltageDim).exponent .amount = 0 ∧
      (toISQHom voltageDim).exponent .luminousIntensity = 0 :=
  ⟨toISQHom_voltageDim_exponent _, toISQHom_voltageDim_exponent _,
    toISQHom_voltageDim_exponent _, toISQHom_voltageDim_exponent _,
    toISQHom_voltageDim_exponent _, toISQHom_voltageDim_exponent _,
    toISQHom_voltageDim_exponent _⟩

-- Ohm = kg m² s⁻³ A⁻².
example :
    (toISQHom resistanceDim).exponent .length = 2 ∧
      (toISQHom resistanceDim).exponent .mass = 1 ∧
      (toISQHom resistanceDim).exponent .time = -3 ∧
      (toISQHom resistanceDim).exponent .current = -2 ∧
      (toISQHom resistanceDim).exponent .temperature = 0 ∧
      (toISQHom resistanceDim).exponent .amount = 0 ∧
      (toISQHom resistanceDim).exponent .luminousIntensity = 0 :=
  ⟨toISQHom_resistanceDim_exponent _, toISQHom_resistanceDim_exponent _,
    toISQHom_resistanceDim_exponent _, toISQHom_resistanceDim_exponent _,
    toISQHom_resistanceDim_exponent _, toISQHom_resistanceDim_exponent _,
    toISQHom_resistanceDim_exponent _⟩

-- Farad = kg⁻¹ m⁻² s⁴ A².
example :
    (toISQHom capacitanceDim).exponent .length = -2 ∧
      (toISQHom capacitanceDim).exponent .mass = -1 ∧
      (toISQHom capacitanceDim).exponent .time = 4 ∧
      (toISQHom capacitanceDim).exponent .current = 2 ∧
      (toISQHom capacitanceDim).exponent .temperature = 0 ∧
      (toISQHom capacitanceDim).exponent .amount = 0 ∧
      (toISQHom capacitanceDim).exponent .luminousIntensity = 0 :=
  ⟨toISQHom_capacitanceDim_exponent _, toISQHom_capacitanceDim_exponent _,
    toISQHom_capacitanceDim_exponent _, toISQHom_capacitanceDim_exponent _,
    toISQHom_capacitanceDim_exponent _, toISQHom_capacitanceDim_exponent _,
    toISQHom_capacitanceDim_exponent _⟩

-- Henry = kg m² s⁻² A⁻².
example :
    (toISQHom inductanceDim).exponent .length = 2 ∧
      (toISQHom inductanceDim).exponent .mass = 1 ∧
      (toISQHom inductanceDim).exponent .time = -2 ∧
      (toISQHom inductanceDim).exponent .current = -2 ∧
      (toISQHom inductanceDim).exponent .temperature = 0 ∧
      (toISQHom inductanceDim).exponent .amount = 0 ∧
      (toISQHom inductanceDim).exponent .luminousIntensity = 0 :=
  ⟨toISQHom_inductanceDim_exponent _, toISQHom_inductanceDim_exponent _,
    toISQHom_inductanceDim_exponent _, toISQHom_inductanceDim_exponent _,
    toISQHom_inductanceDim_exponent _, toISQHom_inductanceDim_exponent _,
    toISQHom_inductanceDim_exponent _⟩

/-! ## C. The laws at concrete values -/

-- Ohm: 6 V = 2 Ω * 3 A, also after moving every coordinate to `SIPrimed`.
example : OhmLaw ⟨6⟩ ⟨2⟩ ⟨3⟩ := by norm_num [OhmLaw]

example : OhmLaw (scaleUnit SI SIPrimed ⟨6⟩) (scaleUnit SI SIPrimed ⟨2⟩)
    (scaleUnit SI SIPrimed ⟨3⟩) :=
  Eq.mpr
    (congrFun (congrFun (congrFun (ohmLaw_isDimensionallyCorrect SIPrimed SI) _) _) _)
    (by norm_num [OhmLaw])

-- Power: 18 W = 6 V * 3 A.
example : PowerLaw ⟨18⟩ ⟨6⟩ ⟨3⟩ := by norm_num [PowerLaw]

example : PowerLaw (scaleUnit SI SIPrimed ⟨18⟩) (scaleUnit SI SIPrimed ⟨6⟩)
    (scaleUnit SI SIPrimed ⟨3⟩) := by
  unfold PowerLaw
  simp only [WithDim.scaleUnit_val, powerDim_eq, voltageDim_eq, currentDim_eq,
    dimScale_SI_SIPrimed]
  norm_num [NNReal.smul_def]

-- RC: 6 s = 2 Ω * 3 F.
example : RCTimeConstant ⟨6⟩ ⟨2⟩ ⟨3⟩ := by norm_num [RCTimeConstant]

example : RCTimeConstant (scaleUnit SI SIPrimed ⟨6⟩) (scaleUnit SI SIPrimed ⟨2⟩)
    (scaleUnit SI SIPrimed ⟨3⟩) :=
  Eq.mpr
    (congrFun (congrFun (congrFun (rcTimeConstant_isDimensionallyCorrect SIPrimed SI) _) _) _)
    (by norm_num [RCTimeConstant])

-- L/R: 2 s = 6 H / 3 Ω.
example : LRTimeConstant ⟨2⟩ ⟨6⟩ ⟨3⟩ := by norm_num [LRTimeConstant]

example : LRTimeConstant (scaleUnit SI SIPrimed ⟨2⟩) (scaleUnit SI SIPrimed ⟨6⟩)
    (scaleUnit SI SIPrimed ⟨3⟩) :=
  Eq.mpr
    (congrFun (congrFun (congrFun (lrTimeConstant_isDimensionallyCorrect SIPrimed SI) _) _) _)
    (by norm_num [LRTimeConstant])

-- Charge: 6 C = 3 A * 2 s, and `chargeOfCurrent` computes it.
example : ChargeLaw ⟨6⟩ ⟨3⟩ ⟨2⟩ := by norm_num [ChargeLaw]

example : ChargeLaw (scaleUnit SI SIPrimed ⟨6⟩) (scaleUnit SI SIPrimed ⟨3⟩)
    (scaleUnit SI SIPrimed ⟨2⟩) :=
  Eq.mpr
    (congrFun (congrFun (congrFun (chargeLaw_isDimensionallyCorrect SIPrimed SI) _) _) _)
    (by norm_num [ChargeLaw])

example : (chargeOfCurrent ⟨3⟩ ⟨2⟩).val = 6 := by
  rw [chargeOfCurrent_val]
  norm_num

-- 1 A in SI units is 3/7 of the `SIPrimed` current unit (charge unit ×7, time unit ×3).
example : (SI.dimScale SIPrimed currentDim : ℝ) = 3 / 7 := by
  rw [dimScale_currentDim]
  have hC : (C𝓭 : Dimension LTMCTDimensionBase) = ofLTMCTDimensionBase 0 0 0 1 0 := rfl
  have hT : (T𝓭 : Dimension LTMCTDimensionBase) = ofLTMCTDimensionBase 0 1 0 0 0 := rfl
  rw [hC, hT, dimScale_SI_SIPrimed, dimScale_SI_SIPrimed]
  norm_num

/-! ## D. Dimensionally wrong laws -/

example : ¬ IsDimensionallyCorrect VoltagePlusCurrent :=
  voltagePlusCurrent_not_isDimensionallyCorrect

example : ¬ IsDimensionallyCorrect RCAsFrequency :=
  rcAsFrequency_not_isDimensionallyCorrect

-- The wrong law holds at `P = 2`, `V = 1`, `I = 1` in SI coordinates, so only a change of units
-- exposes it.
example : VoltagePlusCurrent ⟨2⟩ ⟨1⟩ ⟨1⟩ := by norm_num [VoltagePlusCurrent]

end PhyslibExtTest.Units.ElectricalDimensions
