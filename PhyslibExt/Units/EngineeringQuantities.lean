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
fixtures obtained by instantiating the existing `UnitScale.dimScale` results. The coordinate
formulas `σ = F / A`, `P = τ ω` and `ṁ = ρ v A` commute with every change of positive ISQ unit
scales, and their outputs are restored as typed quantities.

## i. Overview

This pin reuses, and does not redefine, Physlib's `Dimension ISQDimensionBase`, `WithDim`,
`UnitScale` and `UnitScale.dimScale`, Physlib's derived `ISQDimensionBase.charge`, and the
Atlas names `amountDim`, `molarMassDim`, `stressDim` and `energyDim` together with the
rescaling lemmas `dimScale_round_trip`, `dimScale_mul` and `dimScale_one_mul` and the Celsius
counterexample `celsiusToKelvin_two_mul_twenty_ne` from `PhyslibExt.Units.QuantityDimensions`.

In sections A to D the only new content is the engineering exponent dictionary:

* force `M L T⁻²`, power `M L² T⁻³`, mass flow `M T⁻¹`, molar flow `N T⁻¹`,
  impulse `M L T⁻¹`, translational stiffness `M T⁻²`, torsional stiffness per radian
  `M L² T⁻²`, and the Faraday constant (charge per amount) `I T N⁻¹`.

Model inputs of sections A to D:

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

Section E concerns three engineering coordinate formulas. A coordinate `x` of a quantity of
dimension `d` in the unit choice `u1 : UnitScale B` becomes `u1.dimScale u2 d * x` in the unit
choice `u2`. With every input and the output assigned a fixed ISQ dimension, converting the
input coordinates and then evaluating the formula gives the converted output coordinate:

* normal stress `σ = F / A`: a force over a positive area is a stress;
* shaft power `P = τ ω`: a torque (a force times a lever arm) times an angular velocity is a
  power; plane angle is dimensionless, so an angular velocity has the dimension `T⁻¹`;
* mass flow rate `ṁ = ρ v A`: a mass density times a velocity times a positive area is a mass
  flow rate.

Each formula also has a typed form, `normalStress`, `shaftPower` and `massFlowRate`, which takes
`WithDim` inputs, combines them with the `WithDim` product and quotient and casts the result to
the output dimension by a proved dimension identity. Its coordinate is the real formula evaluated
on the input coordinates, so an output computed from erased (real) coordinates is restored to its
dimension by a theorem, not by a coercion. The proofs instantiate the existing `dimScale_mul`,
`dimScale_inv` and `dimScale_round_trip`; no new rescaling law is stated. Area, mass density,
velocity and angular velocity are written as products of base dimensions; no new dimension name
is introduced.

Model inputs of section E:

* scalar values are components in one declared frame: `F` is the force component normal to the
  area, `τ` and `ω` are components about one axis, and `v` is the velocity component normal to
  the area;
* the area is positive, `0 < A`;
* each input and output dimension is fixed as displayed. The results concern these three formulas,
  not arbitrary real-valued functions of coordinates.

Boundaries: the real-coordinate sum of a force and an area commutes with the metre to millimetre
change for no output dimension, and reading `F / A` as a force breaks the commutation. Conversely,
commuting with a change of units does not certify a formula: the empirically wrong `2 F / A`
commutes as well. Dimensional consistency is not empirical correctness, and no such claim is
made.

The body-to-inertial frame and sign dictionary is in `PhyslibExt.Units.EngineeringFrames`.

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
- `forceDim_mul_inv_area`, `torque_mul_angularVelocity`, `density_mul_velocity_mul_area` : the
  dimension identities of the three formulas of section E.
- `dimScale_forceDim_mul_inv_area`, `dimScale_torque_mul_angularVelocity`,
  `dimScale_density_mul_velocity_mul_area` : the factor identities, instances of `dimScale_mul`.
- `normalStress_coord_dimScale`, `shaftPower_coord_dimScale`, `massFlowRate_coord_dimScale` : the
  real-coordinate formulas commute with every change of unit scales.
- `normalStress`, `shaftPower`, `massFlowRate`, with `normalStress_val`, `shaftPower_val`,
  `massFlowRate_val`, `normalStress_dimScale`, `shaftPower_dimScale`, `massFlowRate_dimScale` :
  the restored typed outputs, their coordinates and their conversion.
- `normalStress_coord_round_trip`, `shaftPower_coord_round_trip`,
  `massFlowRate_coord_round_trip` : an output computed in new units and converted back is the
  output computed in the original units, instances of `dimScale_round_trip`.
- `normalStress_si_mm`, `shaftPower_si_mm`, `massFlowRate_si_mm` : nonzero metre to millimetre
  fixtures for all three formulas.
- `forceDim_ne_area`, `force_add_area_not_dimScale`, `normalStress_coord_ne_forceDim`,
  `two_mul_normalStress_coord_dimScale` : the invalid and boundary examples.

## iii. Table of contents

- A. Engineering dimension names and exponents
- B. Dimension identities and invalid identifications
- C. Instances of the existing rescaling results
- D. Concrete fixtures
- E. Unit invariance of three engineering coordinate formulas
  - E.1. Dimension identities of the three formulas
  - E.2. Instances of the existing rescaling results
  - E.3. The real-coordinate formulas commute with a change of units
  - E.4. Restoring the output quantity
  - E.5. Nonzero fixtures
  - E.6. Invalid and boundary examples

## iv. References

- ISO/IEC 80000-1, *Quantities and units — Part 1: General*: the seven ISQ base quantities and
  the dimension of plane angle.
- ISO 80000-3, *Quantities and units — Part 3: Space and time*: angular velocity, and plane
  angle as a quantity of dimension one.
- ISO 80000-4, *Quantities and units — Part 4: Mechanics*: force, normal stress, power,
  impulse, torque, mass flow rate.
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

/-! ## E. Unit invariance of three engineering coordinate formulas -/

/-! ### E.1. Dimension identities of the three formulas -/

/-- A force over an area, as formed by `WithDim` division, has the stress dimension. -/
lemma forceDim_mul_inv_area : forceDim * (single .length ^ (2 : ℕ))⁻¹ = stressDim := by
  decide

/-- A torque (a force times a lever arm) times an angular velocity has the power dimension. Plane
angle is dimensionless, so an angular velocity has the dimension `T⁻¹`. -/
lemma torque_mul_angularVelocity :
    forceDim * single .length * (single .time)⁻¹ = powerDim := by
  decide

/-- A mass density times a velocity times an area has the mass flow rate dimension. -/
lemma density_mul_velocity_mul_area :
    single .mass / single .length ^ (3 : ℕ) * (single .length / single .time) *
      single .length ^ (2 : ℕ) = massFlowDim := by
  decide

/-! ### E.2. Instances of the existing rescaling results -/

/-- The stress factor is the force factor over the area factor (`dimScale_mul` and
`dimScale_inv` with `forceDim_mul_inv_area`). -/
lemma dimScale_forceDim_mul_inv_area (u1 u2 : UnitScale ISQDimensionBase) :
    (u1.dimScale u2 forceDim : ℝ) * (u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ)⁻¹ =
      (u1.dimScale u2 stressDim : ℝ) := by
  rw [← dimScale_inv, ← dimScale_mul, forceDim_mul_inv_area]

/-- The power factor is the torque factor times the angular-velocity factor (`dimScale_mul` with
`torque_mul_angularVelocity`). -/
lemma dimScale_torque_mul_angularVelocity (u1 u2 : UnitScale ISQDimensionBase) :
    (u1.dimScale u2 (forceDim * single .length) : ℝ) * (u1.dimScale u2 (single .time)⁻¹ : ℝ) =
      (u1.dimScale u2 powerDim : ℝ) := by
  rw [← dimScale_mul, torque_mul_angularVelocity]

/-- The mass-flow factor is the product of the density, velocity and area factors
(`dimScale_mul` with `density_mul_velocity_mul_area`). -/
lemma dimScale_density_mul_velocity_mul_area (u1 u2 : UnitScale ISQDimensionBase) :
    (u1.dimScale u2 (single .mass / single .length ^ (3 : ℕ)) : ℝ) *
        (u1.dimScale u2 (single .length / single .time) : ℝ) *
        (u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) =
      (u1.dimScale u2 massFlowDim : ℝ) := by
  rw [← dimScale_mul, ← dimScale_mul, density_mul_velocity_mul_area]

/-! ### E.3. The real-coordinate formulas commute with a change of units -/

/-- Normal stress `σ = F / A` commutes with every change of unit scales: dividing the converted
normal force by the converted positive area gives the converted stress. -/
lemma normalStress_coord_dimScale (u1 u2 : UnitScale ISQDimensionBase) (F A : ℝ)
    (_hA : 0 < A) :
    (u1.dimScale u2 forceDim : ℝ) * F / ((u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) * A) =
      (u1.dimScale u2 stressDim : ℝ) * (F / A) := by
  rw [← dimScale_forceDim_mul_inv_area u1 u2]
  ring

/-- Shaft power `P = τ ω` commutes with every change of unit scales: the converted torque times
the converted angular velocity is the converted power. -/
lemma shaftPower_coord_dimScale (u1 u2 : UnitScale ISQDimensionBase) (τ ω : ℝ) :
    (u1.dimScale u2 (forceDim * single .length) : ℝ) * τ *
        ((u1.dimScale u2 (single .time)⁻¹ : ℝ) * ω) =
      (u1.dimScale u2 powerDim : ℝ) * (τ * ω) := by
  rw [← dimScale_torque_mul_angularVelocity u1 u2]
  ring

/-- Mass flow rate `ṁ = ρ v A` commutes with every change of unit scales: the converted density,
normal velocity and positive area multiply to the converted mass flow rate. -/
lemma massFlowRate_coord_dimScale (u1 u2 : UnitScale ISQDimensionBase) (ρ v A : ℝ)
    (_hA : 0 < A) :
    (u1.dimScale u2 (single .mass / single .length ^ (3 : ℕ)) : ℝ) * ρ *
        ((u1.dimScale u2 (single .length / single .time) : ℝ) * v) *
        ((u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) * A) =
      (u1.dimScale u2 massFlowDim : ℝ) * (ρ * v * A) := by
  rw [← dimScale_density_mul_velocity_mul_area u1 u2]
  ring

/-! ### E.4. Restoring the output quantity -/

/-- The normal stress `σ = F / A` of a normal force `F` on a positive area `A`: the `WithDim`
quotient, cast to `stressDim` by `forceDim_mul_inv_area`. -/
noncomputable def normalStress (F : WithDim forceDim ℝ)
    (A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ) (_hA : 0 < A.val) :
    WithDim stressDim ℝ :=
  WithDim.cast (F / A) forceDim_mul_inv_area

/-- The shaft power `P = τ ω` of a torque `τ` and an angular velocity `ω` about one axis: the
`WithDim` product, cast to `powerDim` by `torque_mul_angularVelocity`. -/
def shaftPower (τ : WithDim (forceDim * single ISQDimensionBase.length) ℝ)
    (ω : WithDim (single ISQDimensionBase.time)⁻¹ ℝ) : WithDim powerDim ℝ :=
  WithDim.cast (τ * ω) torque_mul_angularVelocity

/-- The mass flow rate `ṁ = ρ v A` of a mass density `ρ`, a normal velocity `v` and a positive
area `A`: the `WithDim` product, cast to `massFlowDim` by `density_mul_velocity_mul_area`. -/
def massFlowRate
    (ρ : WithDim (single ISQDimensionBase.mass / single ISQDimensionBase.length ^ (3 : ℕ)) ℝ)
    (v : WithDim (single ISQDimensionBase.length / single ISQDimensionBase.time) ℝ)
    (A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ) (_hA : 0 < A.val) :
    WithDim massFlowDim ℝ :=
  WithDim.cast (ρ * v * A) density_mul_velocity_mul_area

/-- The coordinate of the typed normal stress is `F / A` evaluated on the input coordinates. -/
lemma normalStress_val (F : WithDim forceDim ℝ)
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hA : 0 < A.val) :
    (normalStress F A hA).val = F.val / A.val := by
  rfl

/-- The coordinate of the typed shaft power is `τ ω` evaluated on the input coordinates. -/
lemma shaftPower_val (τ : WithDim (forceDim * single ISQDimensionBase.length) ℝ)
    (ω : WithDim (single ISQDimensionBase.time)⁻¹ ℝ) :
    (shaftPower τ ω).val = τ.val * ω.val := by
  rfl

/-- The coordinate of the typed mass flow rate is `ρ v A` evaluated on the input coordinates. -/
lemma massFlowRate_val
    (ρ : WithDim (single ISQDimensionBase.mass / single ISQDimensionBase.length ^ (3 : ℕ)) ℝ)
    (v : WithDim (single ISQDimensionBase.length / single ISQDimensionBase.time) ℝ)
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hA : 0 < A.val) :
    (massFlowRate ρ v A hA).val = ρ.val * v.val * A.val := by
  rfl

/-- The typed normal stress commutes with every change of unit scales: converting the force and
the positive area and then forming the stress gives the converted stress. -/
lemma normalStress_dimScale (u1 u2 : UnitScale ISQDimensionBase) (F : WithDim forceDim ℝ)
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hA : 0 < A.val) :
    normalStress ⟨(u1.dimScale u2 forceDim : ℝ) * F.val⟩
        ⟨(u1.dimScale u2 (single ISQDimensionBase.length ^ (2 : ℕ)) : ℝ) * A.val⟩
        (mul_pos (NNReal.coe_pos.mpr
          (dimScale_pos u1 u2 (single ISQDimensionBase.length ^ (2 : ℕ)))) hA) =
      ⟨(u1.dimScale u2 stressDim : ℝ) * (normalStress F A hA).val⟩ := by
  apply WithDim.ext
  exact normalStress_coord_dimScale u1 u2 F.val A.val hA

/-- The typed shaft power commutes with every change of unit scales. -/
lemma shaftPower_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (τ : WithDim (forceDim * single ISQDimensionBase.length) ℝ)
    (ω : WithDim (single ISQDimensionBase.time)⁻¹ ℝ) :
    shaftPower ⟨(u1.dimScale u2 (forceDim * single .length) : ℝ) * τ.val⟩
        ⟨(u1.dimScale u2 (single .time)⁻¹ : ℝ) * ω.val⟩ =
      ⟨(u1.dimScale u2 powerDim : ℝ) * (shaftPower τ ω).val⟩ := by
  apply WithDim.ext
  exact shaftPower_coord_dimScale u1 u2 τ.val ω.val

/-- The typed mass flow rate commutes with every change of unit scales. -/
lemma massFlowRate_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (ρ : WithDim (single ISQDimensionBase.mass / single ISQDimensionBase.length ^ (3 : ℕ)) ℝ)
    (v : WithDim (single ISQDimensionBase.length / single ISQDimensionBase.time) ℝ)
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hA : 0 < A.val) :
    massFlowRate ⟨(u1.dimScale u2 (single .mass / single .length ^ (3 : ℕ)) : ℝ) * ρ.val⟩
        ⟨(u1.dimScale u2 (single .length / single .time) : ℝ) * v.val⟩
        ⟨(u1.dimScale u2 (single ISQDimensionBase.length ^ (2 : ℕ)) : ℝ) * A.val⟩
        (mul_pos (NNReal.coe_pos.mpr
          (dimScale_pos u1 u2 (single ISQDimensionBase.length ^ (2 : ℕ)))) hA) =
      ⟨(u1.dimScale u2 massFlowDim : ℝ) * (massFlowRate ρ v A hA).val⟩ := by
  apply WithDim.ext
  exact massFlowRate_coord_dimScale u1 u2 ρ.val v.val A.val hA

/-- Computing the stress in the new units and converting it back restores the stress computed in
the original units (`dimScale_round_trip` at `stressDim`). -/
lemma normalStress_coord_round_trip (u1 u2 : UnitScale ISQDimensionBase) (F A : ℝ)
    (hA : 0 < A) :
    (u2.dimScale u1 stressDim : ℝ) *
        ((u1.dimScale u2 forceDim : ℝ) * F /
          ((u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) * A)) = F / A := by
  rw [normalStress_coord_dimScale u1 u2 F A hA, dimScale_round_trip]

/-- Computing the power in the new units and converting it back restores the power computed in
the original units (`dimScale_round_trip` at `powerDim`). -/
lemma shaftPower_coord_round_trip (u1 u2 : UnitScale ISQDimensionBase) (τ ω : ℝ) :
    (u2.dimScale u1 powerDim : ℝ) *
        ((u1.dimScale u2 (forceDim * single .length) : ℝ) * τ *
          ((u1.dimScale u2 (single .time)⁻¹ : ℝ) * ω)) = τ * ω := by
  rw [shaftPower_coord_dimScale u1 u2 τ ω, dimScale_round_trip]

/-- Computing the mass flow rate in the new units and converting it back restores the mass flow
rate computed in the original units (`dimScale_round_trip` at `massFlowDim`). -/
lemma massFlowRate_coord_round_trip (u1 u2 : UnitScale ISQDimensionBase) (ρ v A : ℝ)
    (hA : 0 < A) :
    (u2.dimScale u1 massFlowDim : ℝ) *
        ((u1.dimScale u2 (single .mass / single .length ^ (3 : ℕ)) : ℝ) * ρ *
          ((u1.dimScale u2 (single .length / single .time) : ℝ) * v) *
          ((u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) * A)) = ρ * v * A := by
  rw [massFlowRate_coord_dimScale u1 u2 ρ v A hA, dimScale_round_trip]

/-! ### E.5. Nonzero fixtures -/

/-- From metres to millimetres, the normal force `5` on the area `2` (stress `5 / 2`) becomes the
force `5000` on the area `2000000`, whose quotient `1 / 400` is the converted stress. -/
lemma normalStress_si_mm :
    (siScale.dimScale mmScale forceDim : ℝ) * 5 = 5000 ∧
      (siScale.dimScale mmScale (single .length ^ (2 : ℕ)) : ℝ) * 2 = 2000000 ∧
      (5000 : ℝ) / 2000000 = (siScale.dimScale mmScale stressDim : ℝ) * (5 / 2) := by
  simp only [forceDim, stressDim, map_div, map_mul, map_pow, dimScale_single, siScale, mmScale]
  norm_num

/-- From metres to millimetres, the torque `3` and the angular velocity `4` (power `12`) become
`3000000` and `4`, whose product `12000000` is the converted power. -/
lemma shaftPower_si_mm :
    (siScale.dimScale mmScale (forceDim * single .length) : ℝ) * 3 = 3000000 ∧
      (siScale.dimScale mmScale (single .time)⁻¹ : ℝ) * 4 = 4 ∧
      (3000000 : ℝ) * 4 = (siScale.dimScale mmScale powerDim : ℝ) * (3 * 4) := by
  simp only [forceDim, powerDim, energyDim, map_div, map_mul, map_pow, map_inv, dimScale_single,
    siScale, mmScale]
  norm_num

/-- From metres to millimetres, the density `1000`, the normal velocity `2` and the area `1 / 100`
(mass flow rate `20`) become `1 / 1000000`, `2000` and `10000`, whose product is the unchanged
mass flow rate `20`. -/
lemma massFlowRate_si_mm :
    (siScale.dimScale mmScale (single .mass / single .length ^ (3 : ℕ)) : ℝ) * 1000 =
        1 / 1000000 ∧
      (siScale.dimScale mmScale (single .length / single .time) : ℝ) * 2 = 2000 ∧
      (siScale.dimScale mmScale (single .length ^ (2 : ℕ)) : ℝ) * (1 / 100) = 10000 ∧
      (1 / 1000000 : ℝ) * 2000 * 10000 =
        (siScale.dimScale mmScale massFlowDim : ℝ) * (1000 * 2 * (1 / 100)) := by
  simp only [massFlowDim, map_div, map_pow, dimScale_single, siScale, mmScale]
  norm_num

/-! ### E.6. Invalid and boundary examples -/

/-- A force and an area have different dimensions, so `WithDim` has no sum of a force and an area
and no cast between them. -/
lemma forceDim_ne_area : forceDim ≠ single .length ^ (2 : ℕ) := by
  decide

/-- The real-coordinate sum of a force and an area commutes with the metre to millimetre change
for no output dimension: commuting with a change of units is a property of the three formulas
with their dimensions, not of every real-valued function of coordinates. -/
lemma force_add_area_not_dimScale :
    ¬ ∃ d : Dimension ISQDimensionBase, ∀ F A : ℝ,
      (siScale.dimScale mmScale forceDim : ℝ) * F +
          (siScale.dimScale mmScale (single .length ^ (2 : ℕ)) : ℝ) * A =
        (siScale.dimScale mmScale d : ℝ) * (F + A) := by
  rintro ⟨d, hd⟩
  have h1 := hd 1 0
  have h2 := hd 0 1
  simp only [forceDim, map_div, map_mul, map_pow, dimScale_single, siScale, mmScale] at h1 h2
  norm_num at h1 h2
  linarith

/-- The output dimension is fixed: read as a force instead of a stress, the quotient `F / A`
fails to commute with the metre to millimetre change at `F = A = 1`. -/
lemma normalStress_coord_ne_forceDim :
    (siScale.dimScale mmScale forceDim : ℝ) * 1 /
        ((siScale.dimScale mmScale (single .length ^ (2 : ℕ)) : ℝ) * 1) ≠
      (siScale.dimScale mmScale forceDim : ℝ) * (1 / 1) := by
  simp only [forceDim, map_div, map_mul, map_pow, dimScale_single, siScale, mmScale]
  norm_num

/-- Commuting with a change of units does not certify a formula: the dimensionally consistent but
empirically wrong stress `2 F / A` commutes as well. -/
lemma two_mul_normalStress_coord_dimScale (u1 u2 : UnitScale ISQDimensionBase) (F A : ℝ)
    (hA : 0 < A) :
    2 * ((u1.dimScale u2 forceDim : ℝ) * F) /
        ((u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) * A) =
      (u1.dimScale u2 stressDim : ℝ) * (2 * F / A) := by
  rw [mul_left_comm]
  exact normalStress_coord_dimScale u1 u2 (2 * F) A hA

end Units.EngineeringQuantities
