/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import PhyslibExt.FluidDynamics.PipeFrictionPorts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Guarded pipe friction checks

Concrete consumers of `PhyslibExt.FluidDynamics.PipeFrictionPorts`: the Blasius smooth-pipe law
`f_D = 0.316 Re ^ (-1/4)` recorded in the Darcy convention for fully developed flow in a circular
tube with a smooth wall (relative roughness `0`) and `4000 < Re < 100000`, and the same law in the
Fanning convention. Water at `Q = 1/1000` m³/s in a smooth tube of diameter `1/20` m and length
`10` m has `Re = 80000 / π`, inside the box; the forward flow has a positive pressure drop, the
reverse flow a negative one, and both dissipate a positive power. A laminar request and requests
at the endpoints of the open interval are rejected, the Fanning record never supplies a Darcy
factor, and inside the box the Fanning value is a quarter of the Darcy one. The guarded chain
applies to the water request, and a steady segment turns the pressure-drop power into an
internal-energy rise. A Colebrook-type record (Haaland's explicit form) at the relative roughness
`1/1000` applies to the same flow in a pipe of that roughness and rejects the smooth request with
the same Reynolds number, and the smooth Blasius record rejects the rough request and a
noncircular duct.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the Blasius records and the requests, and
proves that the water request lies in the Darcy record's box, which the later examples use;
section B defines the rough-pipe record and request.

## iii. Table of contents

- A. The Blasius smooth-pipe law
- B. A rough pipe

## iv. References

- F. M. White, *Fluid Mechanics*, McGraw-Hill, chapter 6 (the Blasius smooth-pipe law, the
  Darcy and Fanning friction factors, and Haaland's explicit form of the Colebrook equation).
-/

@[expose] public section

namespace PhyslibExtTest.FluidDynamics.PipeFrictionPorts

open CorrelationDomains EngineeringScaling _root_.FluidDynamics.PipeFrictionPorts

/-! ## A. The Blasius smooth-pipe law -/

/-- The Blasius smooth-pipe law in the Darcy convention, `f_D = 0.316 Re ^ (-1/4)`, for fully
developed flow in a circular tube with a smooth wall (relative roughness `0`) and
`4000 < Re < 100000`. -/
noncomputable def blasiusDarcy : FrictionCorrelation :=
  powerLawFriction (79 / 250) (-1 / 4) "Blasius smooth-pipe law, in White, Fluid Mechanics"
    FrictionConvention.darcy DuctShape.circularTube FlowDevelopment.fullyDeveloped 0
    {Re | 4000 < Re ∧ Re < 100000} (fun Re hRe => by linarith [hRe.1]) ⟨10000, by norm_num⟩

/-- The same law in the Fanning convention, `f_F = f_D / 4 = 0.079 Re ^ (-1/4)`. -/
noncomputable def blasiusFanning : FrictionCorrelation :=
  powerLawFriction (79 / 1000) (-1 / 4) "Blasius smooth-pipe law, Fanning form"
    FrictionConvention.fanning DuctShape.circularTube FlowDevelopment.fullyDeveloped 0
    {Re | 4000 < Re ∧ Re < 100000} (fun Re hRe => by linarith [hRe.1]) ⟨10000, by norm_num⟩

/-- Isothermal water (`ρ = 1000`, `μ = 1/1000`) at `Q = 1/1000` m³/s in a smooth circular tube
(relative roughness `0`) of diameter `D = 1/20` m, area `A = π D ^ 2 / 4 = π / 1600` m² and length
`L = 10` m: fully developed, `Re = ρ |Q / A| D / μ = 80000 / π ≈ 25465`. -/
noncomputable def waterRequest : FrictionRequest where
  reynolds := 80000 / Real.pi
  relativeRoughness := 0
  ductShape := DuctShape.circularTube
  hydrodynamicDevelopment := FlowDevelopment.fullyDeveloped

/-- The same tube at the laminar `Re = 2000`. -/
noncomputable def laminarRequest : FrictionRequest :=
  { waterRequest with reynolds := 2000 }

/-- The water request lies in the Blasius box: `4000 < 80000 / π < 100000`. -/
lemma blasius_applies_water : blasiusDarcy.DarcyApplies waterRequest := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · change 4000 < 80000 / Real.pi
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_le_four]
  · change 80000 / Real.pi < 100000
    rw [div_lt_iff₀ Real.pi_pos]
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
      (∀ r : FrictionRequest, ¬ blasiusFanning.DarcyApplies r) ∧
      ∀ (Re : ℝ) (hs : Re ∈ blasiusDarcy.validity) (hs' : Re ∈ blasiusFanning.validity),
        blasiusFanning.formula Re hs' = blasiusDarcy.formula Re hs / 4 := by
  refine ⟨?_, fun r => FrictionCorrelation.not_darcyApplies (Or.inl rfl), ?_⟩
  · refine FrictionCorrelation.not_darcyApplies (Or.inr (Or.inr ?_))
    rintro ⟨h1, -⟩
    change (4000 : ℝ) < 2000 at h1
    norm_num at h1
  · intro Re hs hs'
    change 79 / 1000 * Re ^ (-1 / 4 : ℝ) = 79 / 250 * Re ^ (-1 / 4 : ℝ) / 4
    ring

/-- The cited interval is open: requests at the endpoints `Re = 4000` and `Re = 100000` get no
Darcy factor. -/
example : ¬ blasiusDarcy.DarcyApplies { waterRequest with reynolds := 4000 } ∧
    ¬ blasiusDarcy.DarcyApplies { waterRequest with reynolds := 100000 } := by
  refine ⟨FrictionCorrelation.not_darcyApplies (Or.inr (Or.inr ?_)),
    FrictionCorrelation.not_darcyApplies (Or.inr (Or.inr ?_))⟩
  · rintro ⟨h1, -⟩
    change (4000 : ℝ) < 4000 at h1
    exact lt_irrefl _ h1
  · rintro ⟨-, h2⟩
    change (100000 : ℝ) < 100000 at h2
    exact lt_irrefl _ h2

/-- The guarded chain at the water request in the smooth pipe (roughness height `ε = 0`): the
Blasius record was calibrated for the pipe's relative roughness, its coefficient is positive, and
the reverse flow has the same Reynolds number. -/
example :
    blasiusDarcy.relativeRoughness = 0 / (1 / 20) ∧
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
    (by norm_num : (0 : ℝ) < 1 / 1000) (Q := 1 / 1000) (ε := 0)
    (by
      rw [reynoldsNumber_val]
      change 80000 / Real.pi = 1000 * |1 / 1000 / (Real.pi / 1600)| * (1 / 20) / (1 / 1000)
      rw [abs_of_pos (by positivity)]
      field_simp
      ring)
    (by
      change (0 : ℝ) = 0 / (1 / 20)
      norm_num)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

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

/-! ## B. A rough pipe -/

/-- Haaland's explicit form of the Colebrook equation in the Darcy convention,
`1 / √f = -1.8 log₁₀ (6.9 / Re + (ε / D / 3.7) ^ 1.11)`, recorded for fully developed flow in a
circular tube of relative roughness `εD`, with that roughness in its formula. The Reynolds box
`4000 < Re < 10 ^ 8` is supplied here as test data. -/
noncomputable def haalandDarcy (εD : ℝ) : FrictionCorrelation where
  citation := "Haaland's explicit form of the Colebrook equation, in White, Fluid Mechanics"
  convention := FrictionConvention.darcy
  ductShape := DuctShape.circularTube
  hydrodynamicDevelopment := FlowDevelopment.fullyDeveloped
  relativeRoughness := εD
  validity := {Re | 4000 < Re ∧ Re < 100000000}
  validity_pos := fun Re hRe => by linarith [hRe.1]
  validity_nonempty := ⟨10000, by norm_num⟩
  formula Re _ := 1 / (1.8 * Real.logb 10 (6.9 / Re + (εD / 3.7) ^ (1.11 : ℝ))) ^ 2

/-- The water flow of `waterRequest` in a pipe of the same diameter `1/20` m with roughness
height `ε = 1/20000` m (`0.05` mm), so `ε / D = 1/1000` at the same Reynolds number. -/
noncomputable def roughWaterRequest : FrictionRequest :=
  { waterRequest with relativeRoughness := 1 / 1000 }

/-- **The roughness guard can fail.** The rough-pipe record at `ε / D = 1/1000` applies to the
rough request; the smooth request with the same Reynolds number, duct shape and development is
rejected by it, and the smooth Blasius record rejects the rough request. -/
example : (haalandDarcy (1 / 1000)).DarcyApplies roughWaterRequest ∧
    ¬ (haalandDarcy (1 / 1000)).DarcyApplies waterRequest ∧
    ¬ blasiusDarcy.DarcyApplies roughWaterRequest := by
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_, ?_⟩,
    FrictionCorrelation.not_darcyApplies (Or.inr (Or.inl ?_)),
    FrictionCorrelation.not_darcyApplies (Or.inr (Or.inl ?_))⟩
  · change 4000 < 80000 / Real.pi
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_le_four]
  · change 80000 / Real.pi < 100000000
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.two_le_pi]
  · change (0 : ℝ) ≠ 1 / 1000
    norm_num
  · change (1 / 1000 : ℝ) ≠ 0
    norm_num

/-- The duct shape is compared too: the same smooth flow in a noncircular duct gets no factor from
the circular-tube Blasius record. -/
example :
    ¬ blasiusDarcy.DarcyApplies { waterRequest with ductShape := DuctShape.noncircularDuct } := by
  rintro ⟨-, h, -⟩
  exact absurd h (by decide)

end PhyslibExtTest.FluidDynamics.PipeFrictionPorts
