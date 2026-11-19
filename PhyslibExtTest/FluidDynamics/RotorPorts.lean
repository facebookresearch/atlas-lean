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

Concrete consumers of `PhyslibExt.FluidDynamics.RotorPorts`. A compressor: axial inflow without
swirl at radius `1/10`, radial outflow with swirl `150` at radius `3/10` and mass flow `2`, so the
torque on the fluid is `90`; at `ω = 1000` the power on the fluid is `90000` and the shaft power
out `-90000`. Reversing the meridional velocities of both ports reverses the throughflow and with
it the torque, the power and the shaft power: read with the physical inlet, the same ports form a
turbine. A single blade force `(0, 90, 0)` at radius `1` realizes the compressor's torque, so the
Euler power lemma applies with every hypothesis discharged. The outlet represented at another
azimuth and station has the same axial angular-momentum outflow. Ports with equal angular
momentum per unit mass (`1/10 · 150 = 3/10 · 50`) take no torque. The compressor and turbine signs
and the shaft power out follow from the general lemmas at the compressor's numbers, and the
rotor-relative swirl of the compressor ports at `ω = 1000`, `-100` and `-150`, gives `-70` in the
Euler expression instead of the torque `90`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the compressor ports and computes their
torque in both flow directions; section B applies the power, sign and swirl lemmas.

## iii. Table of contents

- A. A compressor and its reversed flow
- B. Power, signs and swirl

## iv. References

- `PhyslibExt.FluidDynamics.RotorPorts`
-/

@[expose] public section

open scoped Matrix
open FluidDynamics.RotorPorts Units.EngineeringFrames

namespace PhyslibExtTest.FluidDynamics.RotorPorts

/-! ## A. A compressor and its reversed flow -/

/-- Inlet of the compressor fixture: axial inflow `100` without swirl at radius `1/10`, through an
annulus of area `1/50` with outward normal `-e₃`, density `1`, pressure `100`. -/
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

/-- Outlet of the compressor fixture: radial outflow `100` with swirl `150` at radius `3/10`,
through a band of area `1/50` with outward normal `e_r`, density `1`, pressure `150`, represented
at azimuth `1`. -/
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

/-- **Nonzero swirl change: a compressor.** The fixture ports carry `ṁ = 2`; with no other external
moment every torque on the fluid satisfying the steady balance is
`τ = 2 (3/10 · 150 - 1/10 · 0) = 90`. At `ω = 1000` (outlet blade speed `300`) the power on the
fluid is `90000 > 0` and the shaft power out `-90000`. -/
lemma fixture_compressor {o : Fin 3 → ℝ} {τ : ℝ}
    (hbal : τ = axialMomentOutflow o fixtureInlet + axialMomentOutflow o fixtureOutlet) :
    fixtureInlet.massOutflow = -2 ∧ fixtureOutlet.massOutflow = 2 ∧ τ = 90 ∧
      (1000 : ℝ) * τ = 90000 ∧ ProcessPorts.workOut (1000 * τ) = -90000 := by
  have hin : fixtureInlet.massOutflow = -2 := by
    simp only [massOutflow_eq, fixtureInlet]
    norm_num
  have hout : fixtureOutlet.massOutflow = 2 := by
    simp only [massOutflow_eq, fixtureOutlet]
    norm_num
  have hτ : τ = 90 := by
    have h := torqueOnFluid_eq (mdot := 2) (Mext := 0) hin hout (by simpa using hbal)
    simp only [fixtureInlet, fixtureOutlet] at h
    norm_num at h
    linarith
  refine ⟨hin, hout, hτ, by rw [hτ]; norm_num, by rw [hτ]; norm_num [ProcessPorts.workOut]⟩

/-- **Sign reversal changes the port interpretation.** Reversing the meridional velocity at both
fixture ports, swirl kept, reverses the throughflow: the port labelled inlet now carries the
signed outflow `+2`, so the throughflow in the labelled orientation is `ṁ = -2`, and every torque
satisfying the steady balance is `τ = -90`. The power on the fluid is `-90000` and the shaft power
out `+90000`: read with the physical inlet, the same ports form a radial-inflow turbine, a
pump-turbine run backward. -/
lemma fixture_reversedFlow {o : Fin 3 → ℝ} {τ : ℝ}
    (hbal : τ = axialMomentOutflow o { fixtureInlet with cz := -100 } +
      axialMomentOutflow o { fixtureOutlet with cr := -100 }) :
    ({ fixtureInlet with cz := -100 } : RotorPort).massOutflow = 2 ∧
      ({ fixtureOutlet with cr := -100 } : RotorPort).massOutflow = -2 ∧ τ = -90 ∧
      (1000 : ℝ) * τ = -90000 ∧ ProcessPorts.workOut (1000 * τ) = 90000 := by
  have hin : ({ fixtureInlet with cz := -100 } : RotorPort).massOutflow = 2 := by
    simp only [massOutflow_eq, fixtureInlet]
    norm_num
  have hout : ({ fixtureOutlet with cr := -100 } : RotorPort).massOutflow = -2 := by
    simp only [massOutflow_eq, fixtureOutlet]
    norm_num
  have hτ : τ = -90 := by
    have hin2 : ({ fixtureInlet with cz := -100 } : RotorPort).massOutflow = -(-2) := by
      rw [hin]; norm_num
    have hout2 : ({ fixtureOutlet with cr := -100 } : RotorPort).massOutflow = -2 := hout
    have h := torqueOnFluid_eq (mdot := -2) (Mext := 0) hin2 hout2 (by simpa using hbal)
    simp only [fixtureInlet, fixtureOutlet] at h
    norm_num at h
    linarith
  refine ⟨hin, hout, hτ, by rw [hτ]; norm_num, by rw [hτ]; norm_num [ProcessPorts.workOut]⟩

/-! ## B. Power, signs and swirl -/

/-- One point represents the whole band: the compressor outlet represented at another azimuth and
axial station has the same axial angular-momentum outflow `90`, for every origin of the shaft
axis. -/
example (o o' : Fin 3 → ℝ) :
    axialMomentOutflow o fixtureOutlet = 90 ∧
      axialMomentOutflow o' { fixtureOutlet with φ := 2, z := 7 } = 90 := by
  rw [axialMomentOutflow_eq, axialMomentOutflow_eq, massOutflow_eq, massOutflow_eq]
  norm_num [fixtureOutlet]

/-- A blade force `(0, 90, 0)` exerted on the fluid at the point `(1, 0, 0)`, about the origin of
the shaft axis, realizes the compressor's torque: it meets the steady balance with the compressor
ports, so `powerOnFluid_eq` applies, and at `ω = 1000` its power on the fluid is `90000`. -/
example :
    axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) =
        axialMomentOutflow 0 fixtureInlet + axialMomentOutflow 0 fixtureOutlet ∧
      rotorPower (ι := Unit) 1000 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) = 90000 := by
  have hin : fixtureInlet.massOutflow = -2 := by
    rw [massOutflow_eq]; norm_num [fixtureInlet]
  have hout : fixtureOutlet.massOutflow = 2 := by
    rw [massOutflow_eq]; norm_num [fixtureOutlet]
  have hτ : axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) = 90 := by
    simp [axialTorque, shaftAxis, cross_apply, dotProduct, Fin.sum_univ_three]
  have hbal : axialTorque (ι := Unit) 0 (fun _ => ![1, 0, 0]) (fun _ => ![0, 90, 0]) =
      axialMomentOutflow 0 fixtureInlet + axialMomentOutflow 0 fixtureOutlet := by
    rw [hτ, axialMomentOutflow_eq, axialMomentOutflow_eq, hin, hout]
    norm_num [fixtureInlet, fixtureOutlet]
  refine ⟨hbal, ?_⟩
  rw [(powerOnFluid_eq hin hout hbal).2.2]
  norm_num [fixtureInlet, fixtureOutlet]

/-- No swirl change: ports with the angular momentum per unit mass `1/10 · 150 = 3/10 · 50` at both
ends take no torque, whatever the rotor speed. -/
example {o : Fin 3 → ℝ} {τ ω : ℝ}
    (hbal : τ = axialMomentOutflow o { fixtureInlet with cθ := 150 } +
      axialMomentOutflow o { fixtureOutlet with cθ := 50 }) :
    τ = 0 ∧ ω * τ = 0 ∧ ProcessPorts.workOut (ω * τ) = 0 := by
  refine torqueOnFluid_eq_zero_of_swirl (mdot := 2) ?_ ?_ hbal ?_
  · rw [massOutflow_eq]; norm_num [fixtureInlet]
  · rw [massOutflow_eq]; norm_num [fixtureOutlet]
  · norm_num [fixtureInlet, fixtureOutlet]

/-- The compressor's numbers (`ṁ = 2`, `ω = 1000`, `U₁ c_θ₁ = 0`, `U₂ c_θ₂ = 45000`) give positive
power on the fluid and negative shaft power out; with the ports exchanged the shaft power out is
positive, a turbine. -/
example :
    0 < (2 : ℝ) * (1000 * (3 / 10) * 150 - 1000 * (1 / 10) * 0) ∧
      ProcessPorts.workOut ((2 : ℝ) * (1000 * (3 / 10) * 150 - 1000 * (1 / 10) * 0)) < 0 ∧
      0 < ProcessPorts.workOut ((2 : ℝ) * (1000 * (1 / 10) * 0 - 1000 * (3 / 10) * 150)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (compressor_iff (mdot := 2) (ω := 1000) (r₁ := 1 / 10) (cθ₁ := 0) (r₂ := 3 / 10)
      (cθ₂ := 150) (by norm_num)).1.2 (by norm_num)
  · exact (compressor_iff (mdot := 2) (ω := 1000) (r₁ := 1 / 10) (cθ₁ := 0) (r₂ := 3 / 10)
      (cθ₂ := 150) (by norm_num)).2.2 (by norm_num)
  · exact (turbine_iff (mdot := 2) (ω := 1000) (r₁ := 3 / 10) (cθ₁ := 150) (r₂ := 1 / 10)
      (cθ₂ := 0) (by norm_num)).1.2 (by norm_num)

/-- The compressor's shaft: with the torque `90` on the fluid and the fluid's reaction `-90` on a
steadily turning rotor, the shaft torque is `90` and the shaft power out at `ω = 1000` is
`-90000`. -/
example {τShaft : ℝ} (hrotor : τShaft + -90 = 0) :
    τShaft = 90 ∧ ProcessPorts.workOut (1000 * τShaft) = -90000 := by
  obtain ⟨h1, h2, -⟩ := shaftPowerOut_eq (ω := 1000) (τ := 90) (τReaction := -90) (mdot := 2)
    (r₁ := 1 / 10) (cθ₁ := 0) (r₂ := 3 / 10) (cθ₂ := 150) hrotor (by norm_num) (by norm_num)
  exact ⟨h1, by rw [h2]; norm_num⟩

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
