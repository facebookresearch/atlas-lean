/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Physlib.ClassicalMechanics.RigidBody.Motion
public import PhyslibExt.CondensedMatter.Elasticity.StressStrain
public import PhyslibExt.Units.QuantityDimensions
import PhyslibExt.Chemistry.Symmetry.GroupRepresentations

/-!
# Engineering ISQ dimensions and concrete conversion fixtures

Engineering dimension names over the seven-base ISQ, their exponents, and unit-conversion
fixtures obtained by instantiating the existing `UnitScale.dimScale` results. The coordinate
formulas `σ = F / A`, `P = τ ω` and `ṁ = ρ v A` commute with every change of positive ISQ unit
scales, and their outputs are restored as typed quantities.
fixtures obtained by instantiating the existing `UnitScale.dimScale` results. A body-to-inertial
frame convention `x_I = o + R x_B` with `R ∈ SO(3)` comes with its active and passive component
maps, the tension-positive mean pressure `p = -tr σ / 3` and the degree-to-radian factor
`π / 180`.

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
Section F states one body-to-inertial frame convention and its sign dictionary.
A body frame is given by the inertial coordinates `o` of its origin and an orientation
`R : Matrix.specialOrthogonalGroup (Fin 3) ℝ`, the carrier Physlib's `RigidBodyMotion` uses; the
columns of `R` are the body axes in inertial components. A point with body coordinates `x_B` has
inertial coordinates `x_I = o + R x_B` (`bodyToInertial`), and the inverse map is
`x_I ↦ Rᵀ (x_I - o)` (`inertialToBody`). Physlib's `RigidBodyMotion.displacement` is this map
with `o` the centre-of-mass position and `x_B` the position relative to the centre of mass
(`displacement_eq_bodyToInertial`). No second rotation type is introduced.
Free vectors (forces, velocities, moments) carry no origin. Their passive component maps are
`v_I = R v_B` (`bodyToInertialVec`) and `v_B = Rᵀ v_I` (`inertialToBodyVec`); the active rotation
of a vector within one frame is `v ↦ R v` (`rotateActive`). The passive map to inertial
components agrees with the active rotation by `R`, and the passive map to body components is the
active rotation by `R⁻¹ = Rᵀ`: turning the frame by `R` turns components by the inverse.
Moments transfer with the orientation, `R (a ⨯₃ b) = (R a) ⨯₃ (R b)`; this is the determinant-one
case of the existing law `(Q a) ⨯₃ (Q b) = det Q • Q (a ⨯₃ b)` for orthogonal `Q`
(`Chemistry.Symmetry.mulVec_cross_mulVec_of_mem_orthogonalGroup`). A reflection of determinant
`-1` reverses cross-product orientation and is not a frame orientation. Torque and energy share
the dimension `M L² T⁻²`, but torque components change with the frame while work-type dot
products do not.
Stress tensors are written with tension positive, and the mean pressure is
`p = -σₘ = -tr σ / 3`, the negative of the existing mean stress `Elasticity.meanStress`: the
hydrostatic stress `-p 1` has pressure `p`, and a uniaxial tension has negative pressure. The
mean pressure is the same in body and inertial components (`σ_I = R σ_B Rᵀ`) and carries the
stress unit. An angle of `θ` degrees is `θ π / 180` radians (`degToRad`); this factor is applied
explicitly, since no change of unit scale rescales a dimensionless coordinate.
Model inputs of section F:
* every orientation is proper orthogonal, `R ∈ SO(3)`, and the inverse component map is `Rᵀ`;
* the origin `o` is an explicit argument, and all coordinates of points are in one explicit
  length unit; changing that unit rescales origin, body and inertial coordinates alike;
* stresses are tension-positive Cauchy stress components in an orthonormal frame.
Non-goals of section F: no new rotation or frame type, no angle type (a degree reading converts
by the explicit factor `degToRad`), no Euler-angle parametrization, no moment transport between
arbitrary reference points, no frame kinematics beyond Physlib's, and no empirical adequacy or
system safety claim.

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
- `bodyToInertial`, `inertialToBody`, `bodyToInertialVec`, `inertialToBodyVec`, `rotateActive` :
  the frame dictionary, with `inertialToBody_bodyToInertial`, `bodyToInertial_inertialToBody`,
  `inertialToBodyVec_bodyToInertialVec`, `bodyToInertialVec_inertialToBodyVec`,
  `bodyToInertial_sub_bodyToInertial`, `bodyToInertialVec_eq_rotateActive`,
  `inertialToBodyVec_eq_rotateActive_inv` and `bodyToInertial_dimScale`.
- `displacement_eq_bodyToInertial`, `inertialToBody_displacement` : Physlib's rigid-body motions
  follow this convention.
- `bodyToInertialVec_cross`, `bodyToInertialVec_moment`, `bodyToInertialVec_dotProduct` : moments
  transfer with the orientation, and dot products are frame independent.
- `meanPressure`, `meanPressure_eq`, `meanPressure_neg_smul_one`, `meanPressure_uniaxial`,
  `meanPressure_conj`, `meanPressure_dimScale` : the tension-positive mean pressure.
- `degToRad`, `degToRad_ninety`, `degToRad_ne_dimScale_one_mul`, `rotZ`,
  `rotZ_mem_specialOrthogonalGroup`, `rotZ_degToRad_ninety` : the degree factor and the rotation
  about the third axis.
- `quarterTurnZ_fixture`, `bodyToInertial_quarterTurnZ_si_mm`,
  `bodyToInertialVec_quarterTurnZ_moment_ne`,
  `reflectX_mem_orthogonalGroup`, `reflectX_not_mem_specialOrthogonalGroup`, `reflectX_cross`,
  `reflectX_cross_fixture` : the quarter-turn fixture and the reflection boundary.

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
- F. Body-to-inertial frame convention and sign dictionary
  - F.1. The body-to-inertial convention
  - F.2. Physlib rigid-body motions use this convention
  - F.3. Moments and work
  - F.4. Mean pressure of a tension-positive stress
  - F.5. Degrees and the rotation about the third axis
  - F.6. Quarter-turn fixtures and the reflection boundary

## iv. References

- ISO/IEC 80000-1, *Quantities and units — Part 1: General*: the seven ISQ base quantities and
  the dimension of plane angle.
- ISO 80000-3, *Quantities and units — Part 3: Space and time*: angular velocity, and plane
  angle as a quantity of dimension one.
- ISO 80000-4, *Quantities and units — Part 4: Mechanics*: force, normal stress, power,
  impulse, torque, mass flow rate.
- ISO 80000-3, *Quantities and units — Part 3: Space and time*: plane angle and the degree
  `π / 180` rad.
- ISO 80000-4, *Quantities and units — Part 4: Mechanics*: force, power, impulse, torque, normal
  stress and pressure.
- L. D. Landau and E. M. Lifshitz, *Mechanics*, Section 32: the motion of a rigid body as a
  translation of its centre of mass and a rotation about it.
- `Physlib.Units.ParametricUnits`, `Physlib.Units.ISQDimensionBase` and
  `PhyslibExt.Units.QuantityDimensions` at the root package's pin.
- Mathlib's `Matrix.specialOrthogonalGroup` and `crossProduct`, Physlib's `RigidBodyMotion` and
  `PhyslibExt.CondensedMatter.Elasticity.StressStrain` at the root package's pin.
-/

@[expose] public section

open Dimension Units.QuantityDimensions
open scoped Matrix

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
/-! ## F. Body-to-inertial frame convention and sign dictionary -/

/-! ### F.1. The body-to-inertial convention -/

/-- The inertial coordinates `x_I = o + R x_B` of the point with body coordinates `x_B`, for a
body frame whose origin has inertial coordinates `o` and whose orientation is `R ∈ SO(3)`. -/
def bodyToInertial (o : Fin 3 → ℝ) (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (xB : Fin 3 → ℝ) : Fin 3 → ℝ :=
  o + (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ xB

/-- The body coordinates `x_B = Rᵀ (x_I - o)` of the point with inertial coordinates `x_I`. -/
def inertialToBody (o : Fin 3 → ℝ) (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (xI : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *ᵥ (xI - o)

/-- The passive component map of a free vector (a force, a velocity, a moment): the inertial
components `v_I = R v_B` of the vector with body components `v_B`. No origin enters. -/
def bodyToInertialVec (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (vB : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vB

/-- The passive component map back: the body components `v_B = Rᵀ v_I` of the free vector with
inertial components `v_I`. -/
def inertialToBodyVec (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (vI : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *ᵥ vI

/-- The active rotation of a vector by `R`: the rotated vector, with both vectors expressed in
one frame. -/
def rotateActive (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v

/-- The passive map to inertial components agrees with the active rotation by `R`. -/
lemma bodyToInertialVec_eq_rotateActive (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (v : Fin 3 → ℝ) : bodyToInertialVec R v = rotateActive R v := by
  rfl

/-- The passive map to body components is the active rotation by `R⁻¹`: turning the frame by `R`
turns components by the inverse. -/
lemma inertialToBodyVec_eq_rotateActive_inv (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (v : Fin 3 → ℝ) : inertialToBodyVec R v = rotateActive R⁻¹ v := by
  simp only [inertialToBodyVec, rotateActive]
  congr 1

/-- The inverse of `x_B ↦ o + R x_B` is `x_I ↦ Rᵀ (x_I - o)`: body coordinates are recovered. -/
lemma inertialToBody_bodyToInertial (o : Fin 3 → ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (xB : Fin 3 → ℝ) :
    inertialToBody o R (bodyToInertial o R xB) = xB := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [inertialToBody, bodyToInertial, add_sub_cancel_left, Matrix.mulVec_mulVec, hT,
    Matrix.one_mulVec]

/-- Inertial coordinates are recovered from body coordinates. -/
lemma bodyToInertial_inertialToBody (o : Fin 3 → ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (xI : Fin 3 → ℝ) :
    bodyToInertial o R (inertialToBody o R xI) = xI := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ) * (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [inertialToBody, bodyToInertial, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec,
    add_sub_cancel]

/-- The passive map to body components inverts the passive map to inertial components. -/
lemma inertialToBodyVec_bodyToInertialVec (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (vB : Fin 3 → ℝ) : inertialToBodyVec R (bodyToInertialVec R vB) = vB := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [inertialToBodyVec, bodyToInertialVec, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]

/-- The passive map to inertial components inverts the passive map to body components. -/
lemma bodyToInertialVec_inertialToBodyVec (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (vI : Fin 3 → ℝ) : bodyToInertialVec R (inertialToBodyVec R vI) = vI := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ) * (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [inertialToBodyVec, bodyToInertialVec, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]

/-- The displacement between two points is a free vector: the frame origin cancels. -/
lemma bodyToInertial_sub_bodyToInertial (o : Fin 3 → ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    bodyToInertial o R x - bodyToInertial o R y = bodyToInertialVec R (x - y) := by
  simp only [bodyToInertial, bodyToInertialVec, Matrix.mulVec_sub, add_sub_add_left_eq_sub]

/-- Units are explicit: expressing the origin and the body coordinates in a new length unit
rescales the inertial coordinates by the same length factor. -/
lemma bodyToInertial_dimScale (u1 u2 : UnitScale ISQDimensionBase) (o : Fin 3 → ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (xB : Fin 3 → ℝ) :
    bodyToInertial ((u1.dimScale u2 (single .length) : ℝ) • o) R
        ((u1.dimScale u2 (single .length) : ℝ) • xB) =
      (u1.dimScale u2 (single .length) : ℝ) • bodyToInertial o R xB := by
  simp only [bodyToInertial, Matrix.mulVec_smul, smul_add]

/-! ### F.2. Physlib rigid-body motions use this convention -/

/-- At time `t`, Physlib's rigid displacement places the body point `y` at `x_I = o + R x_B`,
with `o` the inertial position of the centre of mass, `R` the orientation and `x_B = y - c` the
coordinates of `y` relative to the centre of mass `c`. -/
lemma displacement_eq_bodyToInertial (M : RigidBodyMotion 3) (t : Time) (y : Space 3) :
    (fun k => M.displacement t y k) =
      bodyToInertial (fun k => M.comTrajectory t k) (M.orientation t)
        (fun j => y j - M.centerOfMass j) := by
  funext k
  rw [RigidBodyMotion.displacement_apply]
  simp only [bodyToInertial, Pi.add_apply, Matrix.mulVec, dotProduct]
  ring

/-- The body coordinates of a displaced body point are its coordinates relative to the centre
of mass. -/
lemma inertialToBody_displacement (M : RigidBodyMotion 3) (t : Time) (y : Space 3) :
    inertialToBody (fun k => M.comTrajectory t k) (M.orientation t)
        (fun k => M.displacement t y k) =
      fun j => y j - M.centerOfMass j := by
  rw [displacement_eq_bodyToInertial, inertialToBody_bodyToInertial]

/-! ### F.3. Moments and work -/

/-- Moments transfer between frames with the orientation: the inertial components of `a ⨯₃ b`
are the cross product of the inertial components of `a` and `b`. -/
lemma bodyToInertialVec_cross (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (a b : Fin 3 → ℝ) :
    bodyToInertialVec R (a ⨯₃ b) = bodyToInertialVec R a ⨯₃ bodyToInertialVec R b := by
  have hR := Matrix.mem_specialOrthogonalGroup_iff.mp R.2
  simp only [bodyToInertialVec]
  rw [Chemistry.Symmetry.mulVec_cross_mulVec_of_mem_orthogonalGroup hR.1 a b, hR.2, one_smul]

/-- The moment `x_B ⨯₃ F_B` about the body origin of the force `F_B` applied at the body point
`x_B` has inertial components `(x_I - o) ⨯₃ F_I`: its lever arm runs from the explicit origin
`o` of the body frame. -/
lemma bodyToInertialVec_moment (o : Fin 3 → ℝ) (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (xB FB : Fin 3 → ℝ) :
    bodyToInertialVec R (xB ⨯₃ FB) = (bodyToInertial o R xB - o) ⨯₃ bodyToInertialVec R FB := by
  rw [bodyToInertialVec_cross]
  congr 1
  simp only [bodyToInertial, bodyToInertialVec, add_sub_cancel_left]

/-- Work-type scalars are frame independent: the dot product of two vectors, such as the work
`F ⬝ᵥ d` of a force along a displacement, is the same in body and inertial components. -/
lemma bodyToInertialVec_dotProduct (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (a b : Fin 3 → ℝ) : bodyToInertialVec R a ⬝ᵥ bodyToInertialVec R b = a ⬝ᵥ b := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [bodyToInertialVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hT,
    Matrix.one_mulVec]

/-! ### F.4. Mean pressure of a tension-positive stress -/

/-- The mean pressure `p = -σₘ` of a stress tensor `σ` written with the tension-positive sign
convention: the negative of the mean stress `Elasticity.meanStress σ = tr σ / 3`. -/
noncomputable def meanPressure (σ : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := -Elasticity.meanStress σ

/-- The mean pressure of a tension-positive stress is `p = -tr σ / 3`. -/
lemma meanPressure_eq (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    meanPressure σ = -Matrix.trace σ / 3 := by
  simp only [meanPressure, Elasticity.meanStress]
  ring

/-- The hydrostatic stress `σ = -p 1` has mean pressure `p`. -/
lemma meanPressure_neg_smul_one (p : ℝ) :
    meanPressure (-(p • (1 : Matrix (Fin 3) (Fin 3) ℝ))) = p := by
  simp [meanPressure, Elasticity.meanStress, Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_one]
  ring

/-- A uniaxial tension `s` has mean pressure `-s / 3`, negative for `s > 0`: with tension
positive, a tension lowers the pressure. -/
lemma meanPressure_uniaxial (s : ℝ) : meanPressure (Matrix.diagonal ![s, 0, 0]) = -s / 3 := by
  simp [meanPressure, Elasticity.meanStress, Matrix.trace, Fin.sum_univ_three]
  ring

/-- The mean pressure is the same in body and inertial components: stress components transform
as `σ_I = R σ_B Rᵀ`. -/
lemma meanPressure_conj (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    meanPressure ((R : Matrix (Fin 3) (Fin 3) ℝ) * σ * (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) =
      meanPressure σ := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [meanPressure, Elasticity.meanStress]
  rw [Elasticity.trace_conjugate σ _ hT]

/-- The mean pressure carries the stress unit: rescaling every stress component by the stress
factor rescales the mean pressure by the same factor. -/
lemma meanPressure_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    meanPressure ((u1.dimScale u2 stressDim : ℝ) • σ) =
      (u1.dimScale u2 stressDim : ℝ) * meanPressure σ := by
  simp only [meanPressure, Elasticity.meanStress, Matrix.trace_smul]
  ring

/-! ### F.5. Degrees and the rotation about the third axis -/

/-- The radian measure `θ π / 180` of an angle of `θ` degrees. -/
noncomputable def degToRad (θ : ℝ) : ℝ := θ * Real.pi / 180

/-- Ninety degrees is `π / 2` radians. -/
lemma degToRad_ninety : degToRad 90 = Real.pi / 2 := by
  unfold degToRad
  ring

/-- The degree conversion is an explicit factor, never a change of unit scale: it moves every
nonzero reading, while a dimensionless coordinate does not rescale under any change of
`UnitScale`. -/
lemma degToRad_ne_dimScale_one_mul (u1 u2 : UnitScale ISQDimensionBase) {θ : ℝ} (hθ : θ ≠ 0) :
    degToRad θ ≠ (u1.dimScale u2 1 : ℝ) * θ := by
  rw [dimScale_one_mul]
  unfold degToRad
  intro h
  have h1 : θ * Real.pi = θ * 180 := by
    linarith [h, show θ * Real.pi / 180 * 180 = θ * Real.pi by ring]
  have h2 : Real.pi = 180 := mul_left_cancel₀ hθ h1
  linarith [Real.pi_le_four]

/-- The rotation matrix by the angle `θ` (in radians) about the third axis. -/
noncomputable def rotZ (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- The rotation about the third axis is proper orthogonal. -/
lemma rotZ_mem_specialOrthogonalGroup (θ : ℝ) :
    rotZ θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three] <;>
      nlinarith [Real.cos_sq_add_sin_sq θ]
  · simp [rotZ, Matrix.det_fin_three]
    nlinarith [Real.cos_sq_add_sin_sq θ]

/-- At ninety degrees the rotation about the third axis is the quarter turn `e₁ ↦ e₂`,
`e₂ ↦ -e₁`, `e₃ ↦ e₃`. -/
lemma rotZ_degToRad_ninety : rotZ (degToRad 90) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [degToRad_ninety]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-! ### F.6. Quarter-turn fixtures and the reflection boundary -/

/-- The ninety-degree rotation about the third axis, as a frame orientation. -/
noncomputable def quarterTurnZ : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨rotZ (degToRad 90), rotZ_mem_specialOrthogonalGroup _⟩

/-- The quarter turn on the nonparallel pair `e₁, e₂`: their inertial components are `e₂` and
`-e₁`; the moment `e₁ ⨯₃ e₂ = e₃` has inertial components `e₃`, the cross product of the
transferred pair; and the passive map to body components turns `e₁` to `-e₂`, the opposite way
from the active rotation, which turns it to `e₂`. -/
lemma quarterTurnZ_fixture :
    bodyToInertialVec quarterTurnZ ![1, 0, 0] = ![0, 1, 0] ∧
      bodyToInertialVec quarterTurnZ ![0, 1, 0] = ![-1, 0, 0] ∧
      bodyToInertialVec quarterTurnZ (![1, 0, 0] ⨯₃ ![0, 1, 0]) = ![0, 0, 1] ∧
      bodyToInertialVec quarterTurnZ ![1, 0, 0] ⨯₃ bodyToInertialVec quarterTurnZ ![0, 1, 0] =
        ![0, 0, 1] ∧
      rotateActive quarterTurnZ ![1, 0, 0] = ![0, 1, 0] ∧
      inertialToBodyVec quarterTurnZ ![1, 0, 0] = ![0, -1, 0] := by
  have hq : (quarterTurnZ : Matrix (Fin 3) (Fin 3) ℝ) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    rotZ_degToRad_ninety
  simp only [bodyToInertialVec, rotateActive, inertialToBodyVec, hq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply]

/-- Units and the origin are explicit: the body point `(1, 0, 0)` of the quarter-turned frame with
origin `(2, 0, 0)` lies at `(2, 1, 0)` (metres); from metres to millimetres the length factor is
`1000`, and the origin `(2000, 0, 0)` and the body point `(1000, 0, 0)` give `(2000, 1000, 0)`. -/
lemma bodyToInertial_quarterTurnZ_si_mm :
    bodyToInertial ![2, 0, 0] quarterTurnZ ![1, 0, 0] = ![2, 1, 0] ∧
      (siScale.dimScale mmScale (single .length) : ℝ) = 1000 ∧
      bodyToInertial ![2000, 0, 0] quarterTurnZ ![1000, 0, 0] = ![2000, 1000, 0] := by
  have hq : (quarterTurnZ : Matrix (Fin 3) (Fin 3) ℝ) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    rotZ_degToRad_ninety
  refine ⟨?_, ?_, ?_⟩
  · simp only [bodyToInertial, hq]
    ext i
    fin_cases i <;> simp
  · rw [dimScale_single]
    simp [siScale, mmScale]
  · simp only [bodyToInertial, hq]
    ext i
    fin_cases i <;> simp

/-- Torque is not a scalar energy merely because the dimensions agree: under the quarter turn the
moment `e₂ ⨯₃ e₃ = e₁` has inertial components `e₂`, so its components change with the frame,
unlike the frame-independent dot products of `bodyToInertialVec_dotProduct`. -/
lemma bodyToInertialVec_quarterTurnZ_moment_ne :
    bodyToInertialVec quarterTurnZ (![0, 1, 0] ⨯₃ ![0, 0, 1]) ≠ ![0, 1, 0] ⨯₃ ![0, 0, 1] := by
  have hq : (quarterTurnZ : Matrix (Fin 3) (Fin 3) ℝ) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    rotZ_degToRad_ninety
  simp only [bodyToInertialVec, hq]
  intro h
  have h0 := congrFun h 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply] at h0

/-- The reflection `diag(-1, 1, 1)`, which reverses the first axis. -/
def reflectX : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 1, 1]

/-- The reflection is orthogonal. -/
lemma reflectX_mem_orthogonalGroup : reflectX ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectX, Matrix.diagonal, Matrix.mul_apply]

/-- The reflection has determinant `-1`, so it is not a frame orientation. -/
lemma reflectX_not_mem_specialOrthogonalGroup :
    reflectX ∉ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  intro h
  have hdet := (Matrix.mem_specialOrthogonalGroup_iff.mp h).2
  simp [reflectX, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  norm_num at hdet

/-- A determinant `-1` reflection reverses cross-product orientation:
`(P a) ⨯₃ (P b) = -(P (a ⨯₃ b))`. -/
lemma reflectX_cross (a b : Fin 3 → ℝ) :
    (reflectX *ᵥ a) ⨯₃ (reflectX *ᵥ b) = -(reflectX *ᵥ (a ⨯₃ b)) := by
  have horth : reflectX ∈ Matrix.orthogonalGroup (Fin 3) ℝ := reflectX_mem_orthogonalGroup
  have hdet : reflectX.det = -1 := by
    simp [reflectX, Matrix.det_diagonal, Fin.prod_univ_three]
  rw [Chemistry.Symmetry.mulVec_cross_mulVec_of_mem_orthogonalGroup horth a b, hdet, neg_one_smul]

/-- On `e₁, e₂` the reflection gives `(P e₁) ⨯₃ (P e₂) = -e₃` but `P (e₁ ⨯₃ e₂) = e₃`. -/
lemma reflectX_cross_fixture :
    (reflectX *ᵥ ![1, 0, 0]) ⨯₃ (reflectX *ᵥ ![0, 1, 0]) = ![0, 0, -1] ∧
      reflectX *ᵥ (![1, 0, 0] ⨯₃ ![0, 1, 0]) = ![0, 0, 1] := by
  refine ⟨?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [reflectX, Matrix.mulVec_diagonal, cross_apply]

end Units.EngineeringQuantities
