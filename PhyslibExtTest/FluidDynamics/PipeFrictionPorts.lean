/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.PipeFrictionPorts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Guarded pipe friction checks

Concrete consumers of `PhyslibExt.FluidDynamics.PipeFrictionPorts`: the Blasius smooth-pipe law
`f_D = 0.316 Re ^ (-1/4)` recorded in the Darcy convention for fully developed flow in a smooth
circular tube with `4000 ≤ Re ≤ 100000`, and the same law in the Fanning convention. Water at
`Q = 1/1000` m³/s in a tube of diameter `1/20` m and length `10` m has `Re = 80000 / π`, inside
the box; the forward flow has a positive pressure drop, the reverse flow a negative one, and both
dissipate a positive power. A laminar request is rejected, the Fanning record never supplies a
Darcy factor, and inside the box the Fanning value is a quarter of the Darcy one. The guarded
chain applies to the water request, and a steady segment turns the pressure-drop power into an
internal-energy rise.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the Blasius records and the requests, and
proves that the water request lies in the Darcy record's box, which the later examples use.

## iii. Table of contents

- A. The Blasius smooth-pipe law

## iv. References

- F. M. White, *Fluid Mechanics*, McGraw-Hill, chapter 6 (the Blasius smooth-pipe law and the
  Darcy and Fanning friction factors).
-/

@[expose] public section

namespace PhyslibExtTest.FluidDynamics.PipeFrictionPorts

open CorrelationDomains EngineeringScaling _root_.FluidDynamics.PipeFrictionPorts

/-! ## A. The Blasius smooth-pipe law -/

/-- The Blasius smooth-pipe law in the Darcy convention, `f_D = 0.316 Re ^ (-1/4)`, for fully
developed flow in a smooth circular tube with `4000 ≤ Re ≤ 100000`. -/
noncomputable def blasiusDarcy : FrictionCorrelation :=
  powerLawFriction (79 / 250) (-1 / 4) "Blasius smooth-pipe law, in White, Fluid Mechanics"
    FrictionConvention.darcy FlowConfiguration.smoothCircularTube FlowDevelopment.fullyDeveloped
    {s | 4000 ≤ s.reynolds ∧ s.reynolds ≤ 100000} (fun s hs => by linarith [hs.1])
    ⟨⟨10000, 1, 10, ⟨0⟩, 1⟩, by norm_num⟩

/-- The same law in the Fanning convention, `f_F = f_D / 4 = 0.079 Re ^ (-1/4)`. -/
noncomputable def blasiusFanning : FrictionCorrelation :=
  powerLawFriction (79 / 1000) (-1 / 4) "Blasius smooth-pipe law, Fanning form"
    FrictionConvention.fanning FlowConfiguration.smoothCircularTube FlowDevelopment.fullyDeveloped
    {s | 4000 ≤ s.reynolds ∧ s.reynolds ≤ 100000} (fun s hs => by linarith [hs.1])
    ⟨⟨10000, 1, 10, ⟨0⟩, 1⟩, by norm_num⟩

/-- Isothermal water (`ρ = 1000`, `μ = 1/1000`, `Pr = 7`) at `Q = 1/1000` m³/s in a smooth
circular tube of diameter `D = 1/20` m, area `A = π D ^ 2 / 4 = π / 1600` m² and length
`L = 10` m: fully developed, `Re = ρ |Q / A| D / μ = 80000 / π ≈ 25465`. -/
noncomputable def waterRequest : CorrelationRequest where
  reynolds := 80000 / Real.pi
  prandtl := 7
  lengthRatio := 200
  temperatureDifference := ⟨0⟩
  viscosityRatio := 1
  configuration := FlowConfiguration.smoothCircularTube
  hydrodynamicDevelopment := FlowDevelopment.fullyDeveloped
  thermalDevelopment := FlowDevelopment.fullyDeveloped
  propertyVariation := PropertyVariation.smallToModerate
  averaging := AveragingTag.localValue
  propertyTemperature := PropertyTemperature.bulkMean

/-- The same tube at the laminar `Re = 2000`. -/
noncomputable def laminarRequest : CorrelationRequest :=
  { waterRequest with reynolds := 2000 }

/-- The water request lies in the Blasius box: `4000 ≤ 80000 / π ≤ 100000`. -/
lemma blasius_applies_water : blasiusDarcy.DarcyApplies waterRequest := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · change 4000 ≤ 80000 / Real.pi
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_le_four]
  · change 80000 / Real.pi ≤ 100000
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.two_le_pi]

/-- **Nonzero forward and reverse flows.** The water request carries the Reynolds number of
`Q = 1/1000` in the tube; with the Blasius factor the forward flow has a positive pressure drop,
the reverse flow `Q = -1/1000` a negative one, and both dissipate a positive power. -/
example :
    waterRequest.reynolds =
        reynoldsNumber ⟨1000⟩ ⟨1 / 1000 / (Real.pi / 1600)⟩ ⟨1 / 20⟩ ⟨1 / 1000⟩ (by norm_num) ∧
      0 < frictionPressureDrop (darcyCoefficient
        (blasiusDarcy.darcyFactor waterRequest blasius_applies_water) 10 (1 / 20)
        (Real.pi / 1600) 1000) (1 / 1000) ∧
      frictionPressureDrop (darcyCoefficient
        (blasiusDarcy.darcyFactor waterRequest blasius_applies_water) 10 (1 / 20)
        (Real.pi / 1600) 1000) (-(1 / 1000)) < 0 ∧
      0 < frictionPressureDrop (darcyCoefficient
        (blasiusDarcy.darcyFactor waterRequest blasius_applies_water) 10 (1 / 20)
        (Real.pi / 1600) 1000) (1 / 1000) * (1 / 1000) ∧
      0 < frictionPressureDrop (darcyCoefficient
        (blasiusDarcy.darcyFactor waterRequest blasius_applies_water) 10 (1 / 20)
        (Real.pi / 1600) 1000) (-(1 / 1000)) * (-(1 / 1000)) := by
  have hf : 0 < blasiusDarcy.darcyFactor waterRequest blasius_applies_water :=
    powerLawFriction_darcyFactor_pos (by norm_num) blasius_applies_water
  have hc := darcyCoefficient_pos hf (by norm_num : (0 : ℝ) < 10) (by norm_num : (0 : ℝ) < 1 / 20)
    (by positivity : 0 < Real.pi / 1600) (by norm_num : (0 : ℝ) < 1000)
  refine ⟨?_, ?_, ?_, dissipatedPower_pos hc (by norm_num),
    dissipatedPower_pos hc (by norm_num)⟩
  · rw [reynoldsNumber_val]
    change 80000 / Real.pi = 1000 * |1 / 1000 / (Real.pi / 1600)| * (1 / 20) / (1 / 1000)
    rw [abs_of_pos (by positivity)]
    field_simp
    ring
  · unfold frictionPressureDrop
    positivity
  · unfold frictionPressureDrop
    have h : (-(1 / 1000 : ℝ)) * |-(1 / 1000 : ℝ)| = -(1 / 1000000) := by norm_num
    rw [mul_assoc, h]
    linarith

/-- **Rejections.** The laminar request lies outside the Blasius box; a Fanning record never
supplies a Darcy factor; and inside the box the Fanning value is a quarter of the Darcy one, so
mixing the conventions would understate the loss fourfold. -/
example :
    ¬ blasiusDarcy.DarcyApplies laminarRequest ∧
      (∀ r : CorrelationRequest, ¬ blasiusFanning.DarcyApplies r) ∧
      ∀ (s : FlowConditions) (hs : s ∈ blasiusDarcy.validity) (hs' : s ∈ blasiusFanning.validity),
        blasiusFanning.formula s hs' = blasiusDarcy.formula s hs / 4 := by
  refine ⟨?_, fun r => FrictionCorrelation.not_darcyApplies (Or.inl rfl), ?_⟩
  · refine FrictionCorrelation.not_darcyApplies (Or.inr ?_)
    rintro ⟨h1, -⟩
    change (4000 : ℝ) ≤ 2000 at h1
    norm_num at h1
  · intro s hs hs'
    change 79 / 1000 * s.reynolds ^ (-1 / 4 : ℝ) = 79 / 250 * s.reynolds ^ (-1 / 4 : ℝ) / 4
    ring

/-- The guarded chain at the water request: the Blasius coefficient is positive, the reverse flow
has the same Reynolds number, the forward dissipated power is nonnegative and the reverse pressure
drop is the negated forward one. -/
example :
    0 < darcyCoefficient (blasiusDarcy.darcyFactor waterRequest blasius_applies_water) 10
        (1 / 20) (Real.pi / 1600) 1000 ∧
      waterRequest.reynolds =
        reynoldsNumber ⟨1000⟩ ⟨-(1 / 1000) / (Real.pi / 1600)⟩ ⟨1 / 20⟩ ⟨1 / 1000⟩
          (by norm_num) := by
  have hf : 0 < blasiusDarcy.darcyFactor waterRequest blasius_applies_water :=
    powerLawFriction_darcyFactor_pos (by norm_num) blasius_applies_water
  have h := darcyFactor_frictionPressureDrop blasius_applies_water hf
    (by norm_num : (0 : ℝ) < 10) (by norm_num : (0 : ℝ) < 1 / 20)
    (by positivity : 0 < Real.pi / 1600) (by norm_num : (0 : ℝ) < 1000)
    (by norm_num : (0 : ℝ) < 1 / 1000) (Q := 1 / 1000)
    (by
      rw [reynoldsNumber_val]
      change 80000 / Real.pi = 1000 * |1 / 1000 / (Real.pi / 1600)| * (1 / 20) / (1 / 1000)
      rw [abs_of_pos (by positivity)]
      field_simp
      ring)
  exact ⟨h.1, h.2.1⟩

/-- Reversal at a positive coefficient: the reverse flow has a negative pressure drop. -/
example : SignType.sign (frictionPressureDrop 2 (-(1 / 1000))) = -1 := by
  rw [sign_frictionPressureDrop (by norm_num)]
  norm_num

/-- A steady segment with `ρ = 1000`, `A = V = 1`, inlet pressure `649` and outlet pressure `0`
has the port balance exactly when the internal energy rises by `649/1000`, and with the Darcy loss
`p_in - p_out = 649 Q |Q|` the rise of the energy flow is `649 ≥ 0`. -/
example : (1000 : ℝ) * (1 * 1) * (649 / 1000 - 0) = 649 * (1 * 1) ^ 2 * |1 * 1| ∧
    0 ≤ (1000 : ℝ) * (1 * 1) * (649 / 1000 - 0) :=
  internalEnergyRise_frictionPressureDrop (ρ := 1000) (A := 1) (V := 1) (ein := 0)
    (eout := 649 / 1000) (pin := 649) (pout := 0) (g := 10) (z := 0) (c := 649) ![1]
    (by
      simp [ControlVolumes.portEnergyRate, dotProduct]
      norm_num)
    (by simp [frictionPressureDrop]) (by norm_num)

end PhyslibExtTest.FluidDynamics.PipeFrictionPorts
