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
* the frame dictionary at an arbitrary origin and orientation: the
  inverse maps, the cancelling origin, active against passive maps,
  Physlib's rigid-body motions, and the millimetre length factor;
* moments, work-type dot products and the quarter turn;
* the tension-positive mean pressure, its frame independence and
  stress unit, and the degree factor;
* the reflection boundary: orthogonal, outside `SO(3)`, and
  reversing every cross product.
-/

@[expose] public section

namespace PhyslibExtTest.Units.EngineeringQuantities

open Dimension _root_.Units.QuantityDimensions _root_.Units.EngineeringQuantities
open scoped Matrix

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

/-! ## E. Body-to-inertial frame convention and sign dictionary -/

/-! ### E.1. Frame dictionary -/

-- At an arbitrary origin and orientation the passive maps invert
-- each other, the origin cancels from a displacement, and the
-- passive map to body components is the active rotation by `R⁻¹`.
example (o x y : Fin 3 → ℝ) (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    inertialToBody o R (bodyToInertial o R x) = x ∧
      bodyToInertial o R (inertialToBody o R x) = x ∧
      inertialToBodyVec R (bodyToInertialVec R x) = x ∧
      bodyToInertialVec R (inertialToBodyVec R x) = x ∧
      bodyToInertial o R x - bodyToInertial o R y = bodyToInertialVec R (x - y) ∧
      bodyToInertialVec R x = rotateActive R x ∧
      inertialToBodyVec R x = rotateActive R⁻¹ x :=
  ⟨inertialToBody_bodyToInertial o R x, bodyToInertial_inertialToBody o R x,
    inertialToBodyVec_bodyToInertialVec R x, bodyToInertialVec_inertialToBodyVec R x,
    bodyToInertial_sub_bodyToInertial o R x y, bodyToInertialVec_eq_rotateActive R x,
    inertialToBodyVec_eq_rotateActive_inv R x⟩

-- Physlib's rigid displacement is the frame map from the centre of
-- mass, and the inverse map recovers coordinates relative to it.
example (M : RigidBodyMotion 3) (t : Time) (y : Space 3) :
    (fun k => M.displacement t y k) =
        bodyToInertial (fun k => M.comTrajectory t k) (M.orientation t)
          (fun j => y j - M.centerOfMass j) ∧
      inertialToBody (fun k => M.comTrajectory t k) (M.orientation t)
          (fun k => M.displacement t y k) =
        fun j => y j - M.centerOfMass j :=
  ⟨displacement_eq_bodyToInertial M t y, inertialToBody_displacement M t y⟩

-- From metres to millimetres the frame map commutes with the length
-- factor `1000`: the general rescaling law at the concrete fixture.
example :
    bodyToInertial ((1000 : ℝ) • ![2, 0, 0]) quarterTurnZ ((1000 : ℝ) • ![1, 0, 0]) =
      (1000 : ℝ) • ![2, 1, 0] := by
  have h := bodyToInertial_dimScale siScale mmScale ![2, 0, 0] quarterTurnZ ![1, 0, 0]
  rwa [bodyToInertial_quarterTurnZ_si_mm.2.1, bodyToInertial_quarterTurnZ_si_mm.1] at h

/-! ### E.2. Moments, work and the quarter turn -/

-- At an arbitrary proper rotation, moments transfer with the
-- orientation (with the lever arm measured from the frame origin)
-- and dot products are frame independent.
example (o a b : Fin 3 → ℝ) (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    bodyToInertialVec R (a ⨯₃ b) = bodyToInertialVec R a ⨯₃ bodyToInertialVec R b ∧
      bodyToInertialVec R (a ⨯₃ b) = (bodyToInertial o R a - o) ⨯₃ bodyToInertialVec R b ∧
      bodyToInertialVec R a ⬝ᵥ bodyToInertialVec R b = a ⬝ᵥ b :=
  ⟨bodyToInertialVec_cross R a b, bodyToInertialVec_moment o R a b,
    bodyToInertialVec_dotProduct R a b⟩

-- The quarter turn is `rotZ (degToRad 90)`, a proper rotation. It
-- transfers `e₁, e₂` to `e₂, -e₁`; actively it turns `e₁` to `e₂`,
-- while the passive map to body components turns `e₁` to `-e₂`.
example :
    rotZ (degToRad 90) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] ∧
      rotZ (degToRad 90) ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧
      bodyToInertialVec quarterTurnZ ![1, 0, 0] = ![0, 1, 0] ∧
      bodyToInertialVec quarterTurnZ ![0, 1, 0] = ![-1, 0, 0] ∧
      rotateActive quarterTurnZ ![1, 0, 0] = ![0, 1, 0] ∧
      inertialToBodyVec quarterTurnZ ![1, 0, 0] = ![0, -1, 0] :=
  ⟨rotZ_degToRad_ninety, rotZ_mem_specialOrthogonalGroup _, quarterTurnZ_fixture.1,
    quarterTurnZ_fixture.2.1, quarterTurnZ_fixture.2.2.2.2.1, quarterTurnZ_fixture.2.2.2.2.2⟩

-- Torque is not a scalar energy: under the quarter turn the moment
-- `e₂ ⨯₃ e₃` changes components, while the work-type dot product of
-- the transferred `e₁` with itself stays `1`.
example :
    bodyToInertialVec quarterTurnZ (![0, 1, 0] ⨯₃ ![0, 0, 1]) ≠ ![0, 1, 0] ⨯₃ ![0, 0, 1] ∧
      bodyToInertialVec quarterTurnZ ![1, 0, 0] ⬝ᵥ bodyToInertialVec quarterTurnZ ![1, 0, 0] =
        1 := by
  refine ⟨bodyToInertialVec_quarterTurnZ_moment_ne, ?_⟩
  rw [bodyToInertialVec_dotProduct]
  simp [dotProduct, Fin.sum_univ_three]

/-! ### E.3. Mean pressure and degrees -/

-- With tension positive, the hydrostatic stress `-5 · 1` has pressure
-- `5` and a uniaxial tension `6` has pressure `-2`.
example :
    meanPressure (-((5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))) = 5 ∧
      meanPressure (Matrix.diagonal ![6, 0, 0]) = -2 := by
  refine ⟨meanPressure_neg_smul_one 5, ?_⟩
  rw [meanPressure_uniaxial]
  norm_num

-- The mean pressure is `-tr σ / 3`, frame independent, and scales
-- like a stress: by `1 / 1000` from metres to millimetres.
example (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    meanPressure σ = -Matrix.trace σ / 3 ∧
      meanPressure ((R : Matrix (Fin 3) (Fin 3) ℝ) * σ * (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) =
        meanPressure σ ∧
      meanPressure ((siScale.dimScale mmScale stressDim : ℝ) • σ) =
        1 / 1000 * meanPressure σ := by
  refine ⟨meanPressure_eq σ, meanPressure_conj R σ, ?_⟩
  rw [meanPressure_dimScale, dimScale_si_mm_stressDim]

-- Ninety degrees is `π / 2` radians, and the degree conversion is no
-- change of unit scale, at any pair of scales.
example (u1 u2 : UnitScale ISQDimensionBase) :
    degToRad 90 = Real.pi / 2 ∧ degToRad 90 ≠ (u1.dimScale u2 1 : ℝ) * 90 :=
  ⟨degToRad_ninety, degToRad_ne_dimScale_one_mul u1 u2 (by norm_num)⟩

/-! ### E.4. The reflection boundary -/

-- The reflection `diag(-1, 1, 1)` is orthogonal but not a frame
-- orientation, and it reverses every cross product.
example (a b : Fin 3 → ℝ) :
    reflectX ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧
      reflectX ∉ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧
      (reflectX *ᵥ a) ⨯₃ (reflectX *ᵥ b) = -(reflectX *ᵥ (a ⨯₃ b)) :=
  ⟨reflectX_mem_orthogonalGroup, reflectX_not_mem_specialOrthogonalGroup, reflectX_cross a b⟩

-- On `e₁, e₂` the quarter turn keeps the orientation of the cross
-- product (`e₃` before and after), while the reflection gives `-e₃`.
example :
    bodyToInertialVec quarterTurnZ (![1, 0, 0] ⨯₃ ![0, 1, 0]) = ![0, 0, 1] ∧
      bodyToInertialVec quarterTurnZ ![1, 0, 0] ⨯₃ bodyToInertialVec quarterTurnZ ![0, 1, 0] =
        ![0, 0, 1] ∧
      (reflectX *ᵥ ![1, 0, 0]) ⨯₃ (reflectX *ᵥ ![0, 1, 0]) = ![0, 0, -1] ∧
      reflectX *ᵥ (![1, 0, 0] ⨯₃ ![0, 1, 0]) = ![0, 0, 1] :=
  ⟨quarterTurnZ_fixture.2.2.1, quarterTurnZ_fixture.2.2.2.1, reflectX_cross_fixture.1,
    reflectX_cross_fixture.2⟩

end PhyslibExtTest.Units.EngineeringQuantities
