/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.RotorPorts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Rotor port checks

Concrete consumers of `PhyslibExt.FluidDynamics.RotorPorts`. A compressor with lumped ports: axial
inflow without swirl at the effective radius `1/10`, radial outflow with swirl `150` at radius
`3/10` and mass flow `2`. For rotor forces with the steady lumped balance and a steadily turning
rotor, the torque on the fluid is `90`, the power of the forces at `ω = 1000` is `90000` and the
shaft power out `-90000`. Reversing the meridional velocities of both ports reverses the
throughflow and with it the torque, the power and the shaft power: read with the physical inlet,
the same ports form a turbine. Blade forces `(0, ±90, 0)` at radius `1` meet these balances, so
both fixtures and the compressor and turbine signs apply with every hypothesis discharged. The
representative azimuth and station of a port do not enter its lumped axial angular-momentum flux.
For every port the nonnegative density and area give the lumped mass flow the sign of the outward
normal velocity.
Ports with equal specific axial angular momentum `r c_θ` (`1/10 · 150 = 3/10 · 50`) take no
torque, power or shaft power, while equal swirl velocities at different radii do not suffice.
The rotor-relative swirl of the compressor ports at `ω = 1000`, `-100` and
`-150`, gives `-70` in the Euler expression instead of the torque `90`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the compressor ports and computes the torque,
power and shaft power in both flow directions; section B realizes them by blade forces and applies
the sign, equal-angular-momentum and swirl lemmas.

## iii. Table of contents

- A. A compressor and its reversed flow
- B. Blade forces, signs and swirl

## iv. References

- `PhyslibExt.FluidDynamics.RotorPorts`
-/

@[expose] public section

open scoped Matrix
open FluidDynamics.RotorPorts Units.EngineeringFrames

namespace PhyslibExtTest.FluidDynamics.RotorPorts

/-! ## A. A compressor and its reversed flow -/

/-- Lumped inlet of the compressor fixture: axial inflow `100` without swirl at the effective
radius `1/10`, port area `1/50`, outward normal `-e₃`, density `1`, pressure `100`. -/
noncomputable def fixtureInlet : RotorPort where
  ρ := 1
  A := 1 / 50
  p := 100
  φ := 0
  r := 1 / 10
  z := 0
  cr := 0
  cθ := 0
  cz := 100
  nr := 0
  nz := -1
  normal_unit := by norm_num
  ρ_nonneg := by norm_num
  A_nonneg := by norm_num
  r_nonneg := by norm_num

/-- Lumped outlet of the compressor fixture: radial outflow `100` with swirl `150` at radius
`3/10` (a band of constant radius, whose effective radius is that radius), port area `1/50`,
outward normal `e_r`, density `1`, pressure `150`, represented at azimuth `1`. -/
noncomputable def fixtureOutlet : RotorPort where
  ρ := 1
  A := 1 / 50
  p := 150
  φ := 1
  r := 3 / 10
  z := 1 / 20
  cr := 100
  cθ := 150
  cz := 0
  nr := 1
  nz := 0
  normal_unit := by norm_num
  ρ_nonneg := by norm_num
  A_nonneg := by norm_num
  r_nonneg := by norm_num

/-- **Nonzero swirl change: a compressor.** The fixture ports carry the lumped mass flow `2`. For
forces at points moving with the rotor that meet the steady lumped balance with no other external
moment, the torque on the fluid is `τ = 2 (3/10 · 150 - 1/10 · 0) = 90`; at `ω = 1000` (outlet
blade speed `300`) their power on the fluid is `90000 > 0`, and a steadily turning rotor without
bearing torque has the shaft power out `-90000`. -/
lemma fixture_compressor {ι : Type*} [Fintype ι] {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ}
    {τShaft τReaction : ℝ}
    (hbal : axialTorque o x F = axialMomentFlux o fixtureInlet + axialMomentFlux o fixtureOutlet)
    (hrotor : τShaft + τReaction = 0) (hreact : τReaction = -axialTorque o x F) :
    fixtureInlet.lumpedMassFlow = -2 ∧ fixtureOutlet.lumpedMassFlow = 2 ∧
      axialTorque o x F = 90 ∧ rotorPower 1000 o x F = 90000 ∧
      ProcessPorts.workOut (1000 * τShaft) = -90000 := by
  have hin : fixtureInlet.lumpedMassFlow = -2 := by
    simp only [lumpedMassFlow_eq, fixtureInlet]
    norm_num
  have hout : fixtureOutlet.lumpedMassFlow = 2 := by
    simp only [lumpedMassFlow_eq, fixtureOutlet]
    norm_num
  obtain ⟨htorq, -, hpow⟩ := powerOnFluid_eq (ω := 1000) hin hout hbal
  obtain ⟨-, -, hshaft⟩ := shaftPowerOut_eq (ω := 1000) hin hout hbal hrotor hreact
  refine ⟨hin, hout, ?_, ?_, ?_⟩
  · rw [htorq]; norm_num [fixtureInlet, fixtureOutlet]
  · rw [hpow]; norm_num [fixtureInlet, fixtureOutlet]
  · rw [hshaft]; norm_num [fixtureInlet, fixtureOutlet]

/-- **Sign reversal changes the port interpretation.** Reversing the meridional velocity at both
fixture ports, swirl kept, reverses the throughflow: the port labelled inlet now carries the lumped
mass flow `+2`, so the throughflow in the labelled orientation is `ṁ = -2`. For rotor forces with
the steady lumped balance the torque on the fluid is `-90`, their power at `ω = 1000` is `-90000`,
and a steadily turning rotor has the shaft power out `+90000`: read with the physical inlet, the
same ports form a radial-inflow turbine, a pump-turbine run backward. -/
lemma fixture_reversedFlow {ι : Type*} [Fintype ι] {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ}
    {τShaft τReaction : ℝ}
    (hbal : axialTorque o x F = axialMomentFlux o { fixtureInlet with cz := -100 } +
      axialMomentFlux o { fixtureOutlet with cr := -100 })
    (hrotor : τShaft + τReaction = 0) (hreact : τReaction = -axialTorque o x F) :
    ({ fixtureInlet with cz := -100 } : RotorPort).lumpedMassFlow = 2 ∧
      ({ fixtureOutlet with cr := -100 } : RotorPort).lumpedMassFlow = -2 ∧
      axialTorque o x F = -90 ∧ rotorPower 1000 o x F = -90000 ∧
      ProcessPorts.workOut (1000 * τShaft) = 90000 := by
  have hin : ({ fixtureInlet with cz := -100 } : RotorPort).lumpedMassFlow = -(-2) := by
    simp only [lumpedMassFlow_eq, fixtureInlet]
    norm_num
  have hout : ({ fixtureOutlet with cr := -100 } : RotorPort).lumpedMassFlow = -2 := by
    simp only [lumpedMassFlow_eq, fixtureOutlet]
    norm_num
  obtain ⟨htorq, -, hpow⟩ := powerOnFluid_eq (ω := 1000) hin hout hbal
  obtain ⟨-, -, hshaft⟩ := shaftPowerOut_eq (ω := 1000) hin hout hbal hrotor hreact
  refine ⟨by rw [hin]; norm_num, hout, ?_, ?_, ?_⟩
  · rw [htorq]; norm_num [fixtureInlet, fixtureOutlet]
  · rw [hpow]; norm_num [fixtureInlet, fixtureOutlet]
  · rw [hshaft]; norm_num [fixtureInlet, fixtureOutlet]

/-! ## B. Blade forces, signs and swirl -/

/-- The representative point does not enter: the compressor outlet represented at another azimuth
and axial station has the same lumped axial angular-momentum flux `90`, for every origin of the
shaft axis. -/
example (o o' : Fin 3 → ℝ) :
    axialMomentFlux o fixtureOutlet = 90 ∧
      axialMomentFlux o' { fixtureOutlet with φ := 2, z := 7 } = 90 := by
  rw [axialMomentFlux_eq, axialMomentFlux_eq, lumpedMassFlow_eq, lumpedMassFlow_eq]
  norm_num [fixtureOutlet]

/-- The sign convention of the lumped mass flow holds for every port: with the nonnegative density
and area of a `RotorPort`, outward normal velocity (`cr nr + cz nz ≥ 0`) gives a nonnegative
lumped mass flow, and inward normal velocity a nonpositive one. -/
example (P : RotorPort) :
    (0 ≤ P.cr * P.nr + P.cz * P.nz → 0 ≤ P.lumpedMassFlow) ∧
      (P.cr * P.nr + P.cz * P.nz ≤ 0 → P.lumpedMassFlow ≤ 0) := by
  rw [lumpedMassFlow_eq]
  have hρA : 0 ≤ P.ρ * P.A := mul_nonneg P.ρ_nonneg P.A_nonneg
  exact ⟨fun hv => mul_nonneg hρA hv, fun hv => mul_nonpos_of_nonneg_of_nonpos hρA hv⟩

/-- A blade force `(0, 90, 0)` exerted on the fluid at the point `(1, 0, 0)`, about the origin of
the shaft axis, meets the steady lumped balance with the compressor ports. With the shaft torque
`90` and the reaction `-90`, `fixture_compressor` applies with every hypothesis discharged: the
power on the fluid at `ω = 1000` is `90000` and the shaft power out `-90000`; `compressor_iff`
gives the same signs from `U₁ c_θ₁ = 0 < 45000 = U₂ c_θ₂`. -/
example :
    axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) =
        axialMomentFlux 0 fixtureInlet + axialMomentFlux 0 fixtureOutlet ∧
      rotorPower (ι := Unit) 1000 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) = 90000 ∧
      ProcessPorts.workOut (1000 * 90) = -90000 ∧
      0 < rotorPower (ι := Unit) 1000 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) ∧
      ProcessPorts.workOut (1000 * 90) < 0 := by
  have hτ : axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) = 90 := by
    simp [axialTorque, shaftAxis, cross_apply, dotProduct, Fin.sum_univ_three]
  have hin : fixtureInlet.lumpedMassFlow = -2 := by
    rw [lumpedMassFlow_eq]; norm_num [fixtureInlet]
  have hout : fixtureOutlet.lumpedMassFlow = 2 := by
    rw [lumpedMassFlow_eq]; norm_num [fixtureOutlet]
  have hbal : axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) =
      axialMomentFlux 0 fixtureInlet + axialMomentFlux 0 fixtureOutlet := by
    rw [hτ, axialMomentFlux_eq, axialMomentFlux_eq, hin, hout]
    norm_num [fixtureInlet, fixtureOutlet]
  have hrotor : (90 : ℝ) + -90 = 0 := by norm_num
  have hreact : (-90 : ℝ) =
      -axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) := by rw [hτ]
  obtain ⟨-, -, -, hP, hW⟩ := fixture_compressor hbal hrotor hreact
  obtain ⟨hc1, hc2⟩ := compressor_iff (ω := 1000) (by norm_num : (0 : ℝ) < 2) hin hout hbal
    hrotor hreact
  have hU : (1000 : ℝ) * fixtureInlet.r * fixtureInlet.cθ <
      1000 * fixtureOutlet.r * fixtureOutlet.cθ := by
    norm_num [fixtureInlet, fixtureOutlet]
  exact ⟨hbal, hP, hW, hc1.2 hU, hc2.2 hU⟩

/-- A blade force `(0, -90, 0)` at `(1, 0, 0)` meets the steady lumped balance of the reversed
flow, so `fixture_reversedFlow` applies with every hypothesis discharged. Read with the physical
inlet (the reversed outlet, mass flow `2`), `turbine_iff` gives positive shaft power out and
negative power on the fluid from `U₂ c_θ₂ = 0 < 45000 = U₁ c_θ₁`. -/
example :
    rotorPower (ι := Unit) 1000 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, -90, 0]) = -90000 ∧
      ProcessPorts.workOut (1000 * -90) = 90000 ∧
      0 < ProcessPorts.workOut (1000 * -90) ∧
      rotorPower (ι := Unit) 1000 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, -90, 0]) < 0 := by
  have hτ : axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, -90, 0]) = -90 := by
    simp [axialTorque, shaftAxis, cross_apply, dotProduct, Fin.sum_univ_three]
  have hin : ({ fixtureOutlet with cr := -100 } : RotorPort).lumpedMassFlow = -2 := by
    rw [lumpedMassFlow_eq]; norm_num [fixtureOutlet]
  have hout : ({ fixtureInlet with cz := -100 } : RotorPort).lumpedMassFlow = 2 := by
    rw [lumpedMassFlow_eq]; norm_num [fixtureInlet]
  have hbal : axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, -90, 0]) =
      axialMomentFlux 0 { fixtureInlet with cz := -100 } +
        axialMomentFlux 0 { fixtureOutlet with cr := -100 } := by
    rw [hτ, axialMomentFlux_eq, axialMomentFlux_eq, hin, hout]
    norm_num [fixtureInlet, fixtureOutlet]
  have hbal' : axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, -90, 0]) =
      axialMomentFlux 0 { fixtureOutlet with cr := -100 } +
        axialMomentFlux 0 { fixtureInlet with cz := -100 } := by
    rw [hbal, add_comm]
  have hrotor : (-90 : ℝ) + 90 = 0 := by norm_num
  have hreact : (90 : ℝ) =
      -axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, -90, 0]) := by
    rw [hτ]; norm_num
  obtain ⟨-, -, -, hP, hW⟩ := fixture_reversedFlow hbal hrotor hreact
  obtain ⟨ht1, ht2⟩ := turbine_iff (ω := 1000) (by norm_num : (0 : ℝ) < 2) hin hout hbal'
    hrotor hreact
  have hU : (1000 : ℝ) * ({ fixtureInlet with cz := -100 } : RotorPort).r *
        ({ fixtureInlet with cz := -100 } : RotorPort).cθ <
      1000 * ({ fixtureOutlet with cr := -100 } : RotorPort).r *
        ({ fixtureOutlet with cr := -100 } : RotorPort).cθ := by
    norm_num [fixtureInlet, fixtureOutlet]
  exact ⟨hP, hW, ht1.2 hU, ht2.2 hU⟩

/-- Equal specific angular momentum: for rotor forces with the steady lumped balance between
ports of equal specific axial angular momentum, `1/10 · 150 = 3/10 · 50`, with different swirl
velocities, the torque on the fluid, the power of the forces and the shaft power out of a steadily
turning rotor vanish, whatever the rotor speed. -/
example {ι : Type*} [Fintype ι] {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ} {ω τShaft τReaction : ℝ}
    (hbal : axialTorque o x F = axialMomentFlux o { fixtureInlet with cθ := 150 } +
      axialMomentFlux o { fixtureOutlet with cθ := 50 })
    (hrotor : τShaft + τReaction = 0) (hreact : τReaction = -axialTorque o x F) :
    axialTorque o x F = 0 ∧ rotorPower ω o x F = 0 ∧ ProcessPorts.workOut (ω * τShaft) = 0 := by
  refine torqueOnFluid_eq_zero_of_specificAngularMomentum_eq (mdot := 2) ?_ ?_ hbal ?_ hrotor hreact
  · rw [lumpedMassFlow_eq]; norm_num [fixtureInlet]
  · rw [lumpedMassFlow_eq]; norm_num [fixtureOutlet]
  · norm_num [fixtureInlet, fixtureOutlet]

/-- Equal swirl velocities do not suffice: between ports with the same swirl `150` at the radii
`1/10` and `3/10` the specific axial angular momentum rises from `15` to `45`, and rotor forces with
the steady lumped balance exert the torque `2 · (45 - 15) = 60` on the fluid. -/
example {ι : Type*} [Fintype ι] {o : Fin 3 → ℝ} {x F : ι → Fin 3 → ℝ}
    (hbal : axialTorque o x F = axialMomentFlux o { fixtureInlet with cθ := 150 } +
      axialMomentFlux o { fixtureOutlet with cθ := 150 }) :
    axialTorque o x F = 60 := by
  have hin : ({ fixtureInlet with cθ := 150 } : RotorPort).lumpedMassFlow = -2 := by
    rw [lumpedMassFlow_eq]; norm_num [fixtureInlet]
  have hout : ({ fixtureOutlet with cθ := 150 } : RotorPort).lumpedMassFlow = 2 := by
    rw [lumpedMassFlow_eq]; norm_num [fixtureOutlet]
  rw [(powerOnFluid_eq (ω := 0) hin hout hbal).1]
  norm_num [fixtureInlet, fixtureOutlet]

/-- The swirl in the Euler formula is inertial: at `ω = 1000` the rotor-relative swirl of the
compressor ports is `-100` and `-150`, and the Euler expression with it gives `-70`, not the
torque `90`. -/
example (o : Fin 3 → ℝ) :
    (fixtureInlet.velocity - (1000 : ℝ) • (shaftAxis ⨯₃ (fixtureInlet.point o - o))) ⬝ᵥ
        bodyToInertialVec (cylFrame fixtureInlet.φ) ![0, 1, 0] = -100 ∧
      (fixtureOutlet.velocity - (1000 : ℝ) • (shaftAxis ⨯₃ (fixtureOutlet.point o - o))) ⬝ᵥ
        bodyToInertialVec (cylFrame fixtureOutlet.φ) ![0, 1, 0] = -150 ∧
      (2 : ℝ) * (fixtureOutlet.r * (-150) - fixtureInlet.r * (-100)) = -70 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [relativeSwirl_eq]; norm_num [fixtureInlet]
  · rw [relativeSwirl_eq]; norm_num [fixtureOutlet]
  · norm_num [fixtureInlet, fixtureOutlet]

end PhyslibExtTest.FluidDynamics.RotorPorts
