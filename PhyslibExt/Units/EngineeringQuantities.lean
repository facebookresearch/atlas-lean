/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Units.QuantityDimensions

/-!
# Engineering ISQ dimensions and concrete conversion fixtures

Engineering dimension names over the seven-base ISQ, their exponents, and unit-conversion
fixtures obtained by instantiating the existing `UnitScale.dimScale` results.

## i. Overview

This pin reuses, and does not redefine, Physlib's `Dimension ISQDimensionBase`, `WithDim`,
`UnitScale` and `UnitScale.dimScale`, Physlib's derived `ISQDimensionBase.charge`, and the
Atlas names `amountDim`, `molarMassDim`, `stressDim` and `energyDim` together with the
rescaling lemmas `dimScale_round_trip`, `dimScale_mul` and `dimScale_one_mul` and the Celsius
counterexample `celsiusToKelvin_two_mul_twenty_ne` from `PhyslibExt.Units.QuantityDimensions`.

The only new content is the engineering exponent dictionary:

* force `M L T⁻²`, power `M L² T⁻³`, mass flow `M T⁻¹`, molar flow `N T⁻¹`,
  impulse `M L T⁻¹`, translational stiffness `M T⁻²`, torsional stiffness per radian
  `M L² T⁻²`, and the Faraday constant (charge per amount) `I T N⁻¹`.

Model inputs (hypotheses of the leaf):

* the basis is the seven-base ISQ `ISQDimensionBase`;
* unit choices are `UnitScale`s, so every base unit has a positive magnitude;
* amount of substance is a base quantity, not a particle count, so molar flow `N T⁻¹` is not
  the particle rate `T⁻¹`;
* torque and energy have the same dimension `M L² T⁻²`; the dimension does not record that
  torque is a vector port variable and energy a scalar, so this module does not identify the
  two quantities, only their dimensions;
* plane angle is dimensionless in the ISQ, so `torsionalStiffnessDim` is torque per radian, and
  a degree reading must be converted to radians explicitly: no `UnitScale` change rescales a
  dimensionless coordinate (`dimScale_one_mul`).

Non-goals: no new rescaling theorem, no angle or degree API, no torque type, no SI numerical
value of the Faraday constant, and no empirical adequacy or system safety claim.

## ii. Key results

- `forceDim_exponent`, `powerDim_exponent`, `massFlowDim_exponent`, `molarFlowDim_exponent`,
  `impulseDim_exponent`, `translationalStiffnessDim_exponent`,
  `torsionalStiffnessDim_exponent`, `faradayDim_exponent` : the exponent vectors.
- `forceDim_mul_length`, `stressDim_mul_area`, `powerDim_mul_time`,
  `molarMassDim_mul_molarFlowDim`, `faradayDim_mul_amountDim`,
  `torsionalStiffnessDim_eq_energyDim` : the dimension identities.
- `forceDim_mul_length_ne_div_length`, `massFlowDim_ne_molarFlowDim`,
  `molarFlowDim_ne_inv_time` : the invalid identifications N m = N/m, kg/s = mol/s and
  mol/s = 1/s are refuted.
- `forceDim_dimScale_round_trip`, `stressDim_dimScale_round_trip`, `force_withDim_round_trip`,
  `stress_mul_area_withDim_dimScale`, `dimScale_stress_mul_area`,
  `dimScale_power_mul_time`, `dimScale_molarMass_mul_molarFlow`,
  `dimScale_torsionalStiffness_eq_energy` : instances of the existing rescaling results.
- `siScale`, `mmScale`, `dimScale_si_mm_forceDim`, `dimScale_si_mm_stressDim`,
  `force_fixture_round_trip`, `stress_fixture_round_trip` : the nonzero metre to millimetre
  fixtures.

## iii. Table of contents

- A. Engineering dimension names and exponents
- B. Dimension identities and invalid identifications
- C. Instances of the existing rescaling results
- D. Concrete fixtures

## iv. References

- ISO/IEC 80000-1, *Quantities and units — Part 1: General*: the seven ISQ base quantities and
  the dimension of plane angle.
- ISO 80000-4, *Quantities and units — Part 4: Mechanics*: force, power, impulse, torque.
- `Physlib.Units.ParametricUnits`, `Physlib.Units.ISQDimensionBase` and
  `PhyslibExt.Units.QuantityDimensions` at the root package's pin.
-/

@[expose] public section

open Dimension Units.QuantityDimensions

namespace Units.EngineeringQuantities

/-! ## A. Engineering dimension names and exponents -/

/-- The force dimension `M L T⁻²`. -/
def forceDim : Dimension ISQDimensionBase := single .mass * single .length / single .time ^ 2

/-- The power dimension `M L² T⁻³`, an energy per time. -/
def powerDim : Dimension ISQDimensionBase := energyDim / single .time

/-- The mass flow rate dimension `M T⁻¹`. -/
def massFlowDim : Dimension ISQDimensionBase := single .mass / single .time

/-- The molar flow rate dimension `N T⁻¹`, an amount of substance per time. -/
def molarFlowDim : Dimension ISQDimensionBase := amountDim / single .time

/-- The impulse dimension `M L T⁻¹`, a force times a time. -/
def impulseDim : Dimension ISQDimensionBase := forceDim * single .time

/-- The translational stiffness dimension `M T⁻²`, a force per length. -/
def translationalStiffnessDim : Dimension ISQDimensionBase := forceDim / single .length

/-- The torsional stiffness dimension `M L² T⁻²`: a torque (force times lever arm) per radian,
with plane angle dimensionless. -/
def torsionalStiffnessDim : Dimension ISQDimensionBase := forceDim * single .length

/-- The dimension `I T N⁻¹` of the Faraday constant, an electric charge per amount of
substance. -/
def faradayDim : Dimension ISQDimensionBase := ISQDimensionBase.charge / amountDim

/-- The exponents of `forceDim` at the seven ISQ base quantities. -/
lemma forceDim_exponent (b : ISQDimensionBase) :
    forceDim.exponent b =
      match b with
      | .length => 1
      | .mass => 1
      | .time => -2
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `powerDim` at the seven ISQ base quantities. -/
lemma powerDim_exponent (b : ISQDimensionBase) :
    powerDim.exponent b =
      match b with
      | .length => 2
      | .mass => 1
      | .time => -3
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `massFlowDim` at the seven ISQ base quantities. -/
lemma massFlowDim_exponent (b : ISQDimensionBase) :
    massFlowDim.exponent b =
      match b with
      | .length => 0
      | .mass => 1
      | .time => -1
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `molarFlowDim` at the seven ISQ base quantities. -/
lemma molarFlowDim_exponent (b : ISQDimensionBase) :
    molarFlowDim.exponent b =
      match b with
      | .length => 0
      | .mass => 0
      | .time => -1
      | .current => 0
      | .temperature => 0
      | .amount => 1
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `impulseDim` at the seven ISQ base quantities. -/
lemma impulseDim_exponent (b : ISQDimensionBase) :
    impulseDim.exponent b =
      match b with
      | .length => 1
      | .mass => 1
      | .time => -1
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `translationalStiffnessDim` at the seven ISQ base quantities. -/
lemma translationalStiffnessDim_exponent (b : ISQDimensionBase) :
    translationalStiffnessDim.exponent b =
      match b with
      | .length => 0
      | .mass => 1
      | .time => -2
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `torsionalStiffnessDim` at the seven ISQ base quantities. -/
lemma torsionalStiffnessDim_exponent (b : ISQDimensionBase) :
    torsionalStiffnessDim.exponent b =
      match b with
      | .length => 2
      | .mass => 1
      | .time => -2
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `faradayDim` at the seven ISQ base quantities. -/
lemma faradayDim_exponent (b : ISQDimensionBase) :
    faradayDim.exponent b =
      match b with
      | .length => 0
      | .mass => 0
      | .time => 1
      | .current => 1
      | .temperature => 0
      | .amount => -1
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-! ## B. Dimension identities and invalid identifications -/

/-- A force times a length (a torque, or work) has the energy dimension. -/
lemma forceDim_mul_length : forceDim * single .length = energyDim := by
  decide

/-- A stress times an area is a force. -/
lemma stressDim_mul_area : stressDim * single .length ^ (2 : ℕ) = forceDim := by
  decide

/-- A power times a time is an energy. -/
lemma powerDim_mul_time : powerDim * single .time = energyDim := by
  decide

/-- A molar mass times a molar flow rate is a mass flow rate. -/
lemma molarMassDim_mul_molarFlowDim : molarMassDim * molarFlowDim = massFlowDim := by
  decide

/-- The Faraday constant times an amount of substance is an electric charge. -/
lemma faradayDim_mul_amountDim : faradayDim * amountDim = ISQDimensionBase.charge := by
  decide

/-- Torsional stiffness per radian has the energy dimension, because plane angle is
dimensionless; the dimension alone does not distinguish N m/rad from J. -/
lemma torsionalStiffnessDim_eq_energyDim : torsionalStiffnessDim = energyDim := by
  decide

/-- A newton metre is not a newton per metre. -/
lemma forceDim_mul_length_ne_div_length :
    forceDim * single .length ≠ forceDim / single .length := by
  decide

/-- A mass flow rate (kg/s) is not a molar flow rate (mol/s). -/
lemma massFlowDim_ne_molarFlowDim : massFlowDim ≠ molarFlowDim := by
  decide

/-- A molar flow rate (mol/s) is not a particle rate (1/s): amount is not a count. -/
lemma molarFlowDim_ne_inv_time : molarFlowDim ≠ (single .time)⁻¹ := by
  decide

/-! ## C. Instances of the existing rescaling results -/

/-- Converting a force coordinate from `u1` to `u2` and back returns it
(`dimScale_round_trip` at `forceDim`). -/
lemma forceDim_dimScale_round_trip (u1 u2 : UnitScale ISQDimensionBase) (x : ℝ) :
    (u2.dimScale u1 forceDim : ℝ) * ((u1.dimScale u2 forceDim : ℝ) * x) = x := by
  exact dimScale_round_trip u1 u2 _ x

/-- Converting a stress coordinate from `u1` to `u2` and back returns it
(`dimScale_round_trip` at `stressDim`). -/
lemma stressDim_dimScale_round_trip (u1 u2 : UnitScale ISQDimensionBase) (x : ℝ) :
    (u2.dimScale u1 stressDim : ℝ) * ((u1.dimScale u2 stressDim : ℝ) * x) = x := by
  exact dimScale_round_trip u1 u2 _ x

/-- A force typed as `WithDim forceDim ℝ` converts from `u1` to `u2` and back to itself. -/
lemma force_withDim_round_trip (u1 u2 : UnitScale ISQDimensionBase) (F : WithDim forceDim ℝ) :
    (⟨(u2.dimScale u1 forceDim : ℝ) * ((u1.dimScale u2 forceDim : ℝ) * F.val)⟩ :
      WithDim forceDim ℝ) = F := by
  exact WithDim.ext _ _ (dimScale_round_trip u1 u2 _ F.val)

/-- A stress times an area, formed by `WithDim` multiplication and cast to `forceDim` by
`stressDim_mul_area`, rescales by the force factor when the stress and the area rescale by their
own factors. -/
lemma stress_mul_area_withDim_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (σ : WithDim stressDim ℝ) (A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ) :
    WithDim.cast ((⟨(u1.dimScale u2 stressDim : ℝ) * σ.val⟩ : WithDim stressDim ℝ) *
        (⟨(u1.dimScale u2 (single ISQDimensionBase.length ^ (2 : ℕ)) : ℝ) * A.val⟩ :
          WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ)) stressDim_mul_area =
      (⟨(u1.dimScale u2 forceDim : ℝ) * (WithDim.cast (σ * A) stressDim_mul_area).val⟩ :
        WithDim forceDim ℝ) := by
  apply WithDim.ext
  show ((u1.dimScale u2 stressDim : ℝ) * σ.val) *
        ((u1.dimScale u2 (single ISQDimensionBase.length ^ (2 : ℕ)) : ℝ) * A.val) =
      (u1.dimScale u2 forceDim : ℝ) * (σ.val * A.val)
  rw [← stressDim_mul_area, dimScale_mul]
  ring

/-- The force factor is the stress factor times the area factor (`dimScale_mul` with
`stressDim_mul_area`). -/
lemma dimScale_stress_mul_area (u1 u2 : UnitScale ISQDimensionBase) :
    (u1.dimScale u2 stressDim : ℝ) * (u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) =
      (u1.dimScale u2 forceDim : ℝ) := by
  rw [← dimScale_mul, stressDim_mul_area]

/-- The energy factor is the power factor times the time factor (`dimScale_mul` with
`powerDim_mul_time`). -/
lemma dimScale_power_mul_time (u1 u2 : UnitScale ISQDimensionBase) :
    (u1.dimScale u2 powerDim : ℝ) * (u1.dimScale u2 (single .time) : ℝ) =
      (u1.dimScale u2 energyDim : ℝ) := by
  rw [← dimScale_mul, powerDim_mul_time]

/-- The mass-flow factor is the molar-mass factor times the molar-flow factor (`dimScale_mul`
with `molarMassDim_mul_molarFlowDim`). -/
lemma dimScale_molarMass_mul_molarFlow (u1 u2 : UnitScale ISQDimensionBase) :
    (u1.dimScale u2 molarMassDim : ℝ) * (u1.dimScale u2 molarFlowDim : ℝ) =
      (u1.dimScale u2 massFlowDim : ℝ) := by
  rw [← dimScale_mul, molarMassDim_mul_molarFlowDim]

/-- Torsional stiffness per radian and energy rescale by the same factor under every change of
unit scale, so a degree-to-radian conversion is never a `UnitScale` change and must be applied
explicitly. -/
lemma dimScale_torsionalStiffness_eq_energy (u1 u2 : UnitScale ISQDimensionBase) :
    u1.dimScale u2 torsionalStiffnessDim = u1.dimScale u2 energyDim := by
  rw [torsionalStiffnessDim_eq_energyDim]

/-! ## D. Concrete fixtures -/

/-- The base-unit scale with magnitude `1` at every base quantity (metre, kilogram, second,
ampere, kelvin, mole, candela). -/
noncomputable def siScale : UnitScale ISQDimensionBase where
  scale _ := 1
  scale_pos _ := one_pos

/-- The scale `siScale` with the length unit replaced by the millimetre, of magnitude
`1 / 1000` metre. -/
noncomputable def mmScale : UnitScale ISQDimensionBase where
  scale b := if b = .length then 1 / 1000 else 1
  scale_pos b := by
    split_ifs
    · norm_num
    · exact one_pos

/-- From metres to millimetres, a force coordinate is multiplied by `1000`
(`1 kg m s⁻² = 1000 kg mm s⁻²`). -/
lemma dimScale_si_mm_forceDim : (siScale.dimScale mmScale forceDim : ℝ) = 1000 := by
  simp only [UnitScale.dimScale, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Finset.prod_eq_single ISQDimensionBase.length]
  · simp [siScale, mmScale, forceDim_exponent]
  · intro b _ hb
    simp [siScale, mmScale, hb]
  · simp

/-- From metres to millimetres, a stress coordinate is multiplied by `1 / 1000`
(`1 kg m⁻¹ s⁻² = 1 / 1000 kg mm⁻¹ s⁻²`). -/
lemma dimScale_si_mm_stressDim : (siScale.dimScale mmScale stressDim : ℝ) = 1 / 1000 := by
  simp only [UnitScale.dimScale, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Finset.prod_eq_single ISQDimensionBase.length]
  · rw [show stressDim.exponent ISQDimensionBase.length = -1 from by decide]
    simp [siScale, mmScale, Real.rpow_neg_one]
  · intro b _ hb
    simp [siScale, mmScale, hb]
  · simp

/-- The nonzero force `5` (base units) becomes `5000` in the millimetre scale and converts back
to `5`. -/
lemma force_fixture_round_trip :
    (siScale.dimScale mmScale forceDim : ℝ) * 5 = 5000 ∧
      (mmScale.dimScale siScale forceDim : ℝ) * ((siScale.dimScale mmScale forceDim : ℝ) * 5) =
        5 := by
  constructor
  · rw [dimScale_si_mm_forceDim]; norm_num
  · exact dimScale_round_trip siScale mmScale forceDim 5

/-- The nonzero stress `2` (base units) becomes `1 / 500` in the millimetre scale and converts
back to `2`. -/
lemma stress_fixture_round_trip :
    (siScale.dimScale mmScale stressDim : ℝ) * 2 = 1 / 500 ∧
      (mmScale.dimScale siScale stressDim : ℝ) * ((siScale.dimScale mmScale stressDim : ℝ) * 2) =
        2 := by
  constructor
  · rw [dimScale_si_mm_stressDim]; norm_num
  · exact dimScale_round_trip siScale mmScale stressDim 2

-- Torque and energy share a dimension (`forceDim_mul_length`); the Celsius scale is affine,
-- reused verbatim from `PhyslibExt.Units.QuantityDimensions`.
example : celsiusToKelvin (2 * 20) ≠ 2 * celsiusToKelvin 20 :=
  celsiusToKelvin_two_mul_twenty_ne

end Units.EngineeringQuantities
