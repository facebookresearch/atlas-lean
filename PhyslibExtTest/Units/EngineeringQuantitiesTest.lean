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
  `1000`, a stress coordinate by `1 / 1000`, and both round-trip.
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

end PhyslibExtTest.Units.EngineeringQuantities
