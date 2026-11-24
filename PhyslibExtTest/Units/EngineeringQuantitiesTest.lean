/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Units.EngineeringQuantities

/-!
# Tests for `PhyslibExt.Units.EngineeringQuantities`

* the exponents of the eight engineering dimensions at all seven ISQ
  base quantities;
* the dimension identities (a stress times an area is a force, a
  power times a time is an energy, torsional stiffness per radian
  has the energy dimension) and the refuted identifications;
* the metre-to-millimetre fixtures: a force coordinate scales by
  `1000`, a stress coordinate by `1 / 1000`, and both round-trip;
* the unit invariance of `σ = F / A`, `P = τ ω` and `ṁ = ρ v A`: the
  dimension and factor identities, commutation with every change of
  unit scales, the typed outputs on nonzero coordinates, a round trip,
  the metre-to-millimetre fixtures and the boundary examples.
-/

@[expose] public section

namespace PhyslibExtTest.Units.EngineeringQuantities

open Dimension _root_.Units.QuantityDimensions _root_.Units.EngineeringQuantities

/-! ## A. Exponents -/

-- `forceDim = M L T⁻²`.
example :
    forceDim.exponent .length = 1 ∧ forceDim.exponent .mass = 1 ∧
      forceDim.exponent .time = -2 ∧ forceDim.exponent .current = 0 ∧
      forceDim.exponent .temperature = 0 ∧ forceDim.exponent .amount = 0 ∧
      forceDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact forceDim_exponent _

-- `powerDim = M L² T⁻³`.
example :
    powerDim.exponent .length = 2 ∧ powerDim.exponent .mass = 1 ∧
      powerDim.exponent .time = -3 ∧ powerDim.exponent .current = 0 ∧
      powerDim.exponent .temperature = 0 ∧ powerDim.exponent .amount = 0 ∧
      powerDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact powerDim_exponent _

-- `massFlowDim = M T⁻¹` and `molarFlowDim = N T⁻¹` differ.
example :
    massFlowDim.exponent .mass = 1 ∧ molarFlowDim.exponent .amount = 1 ∧
      massFlowDim ≠ molarFlowDim :=
  ⟨massFlowDim_exponent _, molarFlowDim_exponent _, massFlowDim_ne_molarFlowDim⟩

-- `faradayDim = I T N⁻¹`.
example :
    faradayDim.exponent .length = 0 ∧ faradayDim.exponent .mass = 0 ∧
      faradayDim.exponent .time = 1 ∧ faradayDim.exponent .current = 1 ∧
      faradayDim.exponent .temperature = 0 ∧ faradayDim.exponent .amount = -1 ∧
      faradayDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact faradayDim_exponent _

/-! ## B. Identities and invalid identifications -/

-- A stress times an area is a force; a power times a time is an energy.
example :
    stressDim * single .length ^ (2 : ℕ) = forceDim ∧
      powerDim * single .time = energyDim ∧
      torsionalStiffnessDim = energyDim :=
  ⟨stressDim_mul_area, powerDim_mul_time, torsionalStiffnessDim_eq_energyDim⟩

-- A molar mass times a molar flow is a mass flow; a Faraday constant
-- times an amount is a charge.
example :
    molarMassDim * molarFlowDim = massFlowDim ∧
      faradayDim * amountDim = ISQDimensionBase.charge :=
  ⟨molarMassDim_mul_molarFlowDim, faradayDim_mul_amountDim⟩

-- N m is not N/m, and mol/s is not 1/s.
example :
    forceDim * single .length ≠ forceDim / single .length ∧
      molarFlowDim ≠ (single .time)⁻¹ :=
  ⟨forceDim_mul_length_ne_div_length, molarFlowDim_ne_inv_time⟩

/-! ## C. Rescaling instances and fixtures -/

-- The force factor is the stress factor times the area factor, at
-- arbitrary unit scales.
example (u1 u2 : UnitScale ISQDimensionBase) :
    (u1.dimScale u2 stressDim : ℝ) * (u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) =
      (u1.dimScale u2 forceDim : ℝ) :=
  dimScale_stress_mul_area u1 u2

-- From metres to millimetres: force ×1000, stress ×(1/1000).
example :
    (siScale.dimScale mmScale forceDim : ℝ) = 1000 ∧
      (siScale.dimScale mmScale stressDim : ℝ) = 1 / 1000 :=
  ⟨dimScale_si_mm_forceDim, dimScale_si_mm_stressDim⟩

-- The nonzero fixtures round-trip: force `5 ↔ 5000`, stress `2 ↔ 1/500`.
example :
    (siScale.dimScale mmScale forceDim : ℝ) * 5 = 5000 ∧
      (mmScale.dimScale siScale forceDim : ℝ) * ((siScale.dimScale mmScale forceDim : ℝ) * 5) =
        5 ∧
      (siScale.dimScale mmScale stressDim : ℝ) * 2 = 1 / 500 ∧
      (mmScale.dimScale siScale stressDim : ℝ) * ((siScale.dimScale mmScale stressDim : ℝ) * 2) =
        2 :=
  ⟨force_fixture_round_trip.1, force_fixture_round_trip.2,
    stress_fixture_round_trip.1, stress_fixture_round_trip.2⟩

-- Torsional stiffness per radian and energy rescale identically, so
-- no unit-scale change performs a degree-to-radian conversion.
example (u1 u2 : UnitScale ISQDimensionBase) :
    u1.dimScale u2 torsionalStiffnessDim = u1.dimScale u2 energyDim :=
  dimScale_torsionalStiffness_eq_energy u1 u2

/-! ## D. Unit invariance of three engineering formulas -/

-- The dimension identities of `σ = F / A`, `P = τ ω` and `ṁ = ρ v A`.
example :
    forceDim * (single .length ^ (2 : ℕ))⁻¹ = stressDim ∧
      forceDim * single .length * (single .time)⁻¹ = powerDim ∧
      single .mass / single .length ^ (3 : ℕ) * (single .length / single .time) *
          single .length ^ (2 : ℕ) = massFlowDim :=
  ⟨forceDim_mul_inv_area, torque_mul_angularVelocity, density_mul_velocity_mul_area⟩

-- The power factor is the torque factor times the angular-velocity
-- factor, at arbitrary unit scales.
example (u1 u2 : UnitScale ISQDimensionBase) :
    (u1.dimScale u2 (forceDim * single .length) : ℝ) * (u1.dimScale u2 (single .time)⁻¹ : ℝ) =
      (u1.dimScale u2 powerDim : ℝ) :=
  dimScale_torque_mul_angularVelocity u1 u2

-- The three coordinate formulas commute with every change of unit
-- scales.
example (u1 u2 : UnitScale ISQDimensionBase) (F τ ω ρ v A : ℝ) (hA : 0 < A) :
    (u1.dimScale u2 forceDim : ℝ) * F / ((u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) * A) =
        (u1.dimScale u2 stressDim : ℝ) * (F / A) ∧
      (u1.dimScale u2 (forceDim * single .length) : ℝ) * τ *
          ((u1.dimScale u2 (single .time)⁻¹ : ℝ) * ω) =
        (u1.dimScale u2 powerDim : ℝ) * (τ * ω) ∧
      (u1.dimScale u2 (single .mass / single .length ^ (3 : ℕ)) : ℝ) * ρ *
          ((u1.dimScale u2 (single .length / single .time) : ℝ) * v) *
          ((u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) * A) =
        (u1.dimScale u2 massFlowDim : ℝ) * (ρ * v * A) :=
  ⟨normalStress_coord_dimScale u1 u2 F A hA, shaftPower_coord_dimScale u1 u2 τ ω,
    massFlowRate_coord_dimScale u1 u2 ρ v A hA⟩

-- The typed outputs evaluate the formulas on nonzero coordinates:
-- stress `5 / 2`, power `12` and mass flow rate `20`.
example :
    (normalStress ⟨5⟩ ⟨2⟩ (by norm_num)).val = 5 / 2 ∧ (shaftPower ⟨3⟩ ⟨4⟩).val = 12 ∧
      (massFlowRate ⟨1000⟩ ⟨2⟩ ⟨1 / 100⟩ (by norm_num)).val = 20 := by
  refine ⟨normalStress_val _ _, ?_, ?_⟩
  · rw [shaftPower_val]; norm_num
  · rw [massFlowRate_val]; norm_num

-- The typed stress commutes with every change of unit scales, whatever
-- proof of positivity of the converted area is supplied.
example (u1 u2 : UnitScale ISQDimensionBase) (F : WithDim forceDim ℝ)
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hA : 0 < A.val)
    (hA' : 0 < (u1.dimScale u2 (single ISQDimensionBase.length ^ (2 : ℕ)) : ℝ) * A.val) :
    normalStress ⟨(u1.dimScale u2 forceDim : ℝ) * F.val⟩
        ⟨(u1.dimScale u2 (single ISQDimensionBase.length ^ (2 : ℕ)) : ℝ) * A.val⟩ hA' =
      ⟨(u1.dimScale u2 stressDim : ℝ) * (normalStress F A hA).val⟩ :=
  normalStress_dimScale u1 u2 F hA

-- A power computed in new units and converted back is the power
-- computed in the original units.
example (u1 u2 : UnitScale ISQDimensionBase) (τ ω : ℝ) :
    (u2.dimScale u1 powerDim : ℝ) *
        ((u1.dimScale u2 (forceDim * single .length) : ℝ) * τ *
          ((u1.dimScale u2 (single .time)⁻¹ : ℝ) * ω)) = τ * ω :=
  shaftPower_coord_round_trip u1 u2 τ ω

-- From metres to millimetres: the stress `5 / 2` becomes `1 / 400`, the
-- power `12` becomes `12000000`, and the mass flow rate `20` is unchanged.
example :
    (5000 : ℝ) / 2000000 = (siScale.dimScale mmScale stressDim : ℝ) * (5 / 2) ∧
      (3000000 : ℝ) * 4 = (siScale.dimScale mmScale powerDim : ℝ) * (3 * 4) ∧
      (1 / 1000000 : ℝ) * 2000 * 10000 =
        (siScale.dimScale mmScale massFlowDim : ℝ) * (1000 * 2 * (1 / 100)) :=
  ⟨normalStress_si_mm.2.2, shaftPower_si_mm.2.2, massFlowRate_si_mm.2.2.2⟩

-- A force is not an area, and the real sum of a force and an area
-- commutes with the metre to millimetre change for no output dimension.
example :
    forceDim ≠ single .length ^ (2 : ℕ) ∧
      ¬ ∃ d : Dimension ISQDimensionBase, ∀ F A : ℝ,
        (siScale.dimScale mmScale forceDim : ℝ) * F +
            (siScale.dimScale mmScale (single .length ^ (2 : ℕ)) : ℝ) * A =
          (siScale.dimScale mmScale d : ℝ) * (F + A) :=
  ⟨forceDim_ne_area, force_add_area_not_dimScale⟩

-- Reading `F / A` as a force breaks the commutation, while the
-- empirically wrong `2 F / A` commutes: dimensional consistency does not
-- certify a formula.
example (u1 u2 : UnitScale ISQDimensionBase) (F A : ℝ) (hA : 0 < A) :
    (siScale.dimScale mmScale forceDim : ℝ) * 1 /
          ((siScale.dimScale mmScale (single .length ^ (2 : ℕ)) : ℝ) * 1) ≠
        (siScale.dimScale mmScale forceDim : ℝ) * (1 / 1) ∧
      2 * ((u1.dimScale u2 forceDim : ℝ) * F) /
          ((u1.dimScale u2 (single .length ^ (2 : ℕ)) : ℝ) * A) =
        (u1.dimScale u2 stressDim : ℝ) * (2 * F / A) :=
  ⟨normalStress_coord_ne_forceDim, two_mul_normalStress_coord_dimScale u1 u2 F A hA⟩

end PhyslibExtTest.Units.EngineeringQuantities
