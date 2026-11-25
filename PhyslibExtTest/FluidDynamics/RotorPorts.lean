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

For the actuator disk: the disk with `U∞ = 3`, `U_d = 2`, `U_w = 1` satisfies the port laws, has
induction factor `1/3`, extracts the power `8` and reaches the Betz limit `C_P = 16/27`; at zero
freestream no coefficient normalizes a nonzero power; without extraction the port laws leave the
disk speed undetermined; and the state built from the induction factor `1/5` has the power
coefficient `64/125`, below the limit.

For the hovering rotor: the disk in still air with `ρ = 1`, `A = 2`, induced velocity `3` and far
wake `6` satisfies the port laws, has thrust `36 = 2 ρ A v_i²`, induced velocity `3 = √(36 / 4)`
and induced power `108`; the wind-extraction normalization vanishes in hover; and the state with
every speed reversed keeps the port laws and the thrust but is not powered, and its induced
velocity is not the square root. The energy balance still gives the reversed state the induced
power `-108`, and a still-air state with no force the induced power `0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the compressor ports and computes the torque,
power and shaft power in both flow directions; section B realizes them by blade forces and applies
the sign, equal-angular-momentum and swirl lemmas; section C checks the actuator disk and section D
the hovering rotor.

## iii. Table of contents

- A. A compressor and its reversed flow
- B. Blade forces, signs and swirl
- C. The actuator disk and the Betz limit
- D. The hovering rotor

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

/-! ## C. The actuator disk and the Betz limit -/

/-- The Betz-optimal fixture: `ρ = 1`, `A = 1`, `U∞ = 3`, `U_d = 2`, `U_w = 1`, gauge pressures
`p∞ = 0`, `p⁺ = 5/2`, `p⁻ = -3/2`, force `4`. -/
noncomputable def betzFixture : ActuatorDisk where
  ρ := 1
  A := 1
  uInf := 3
  uDisk := 2
  uWake := 1
  pAmb := 0
  pUp := 5 / 2
  pDown := -3 / 2
  force := 4

/-- **`a = 1/3` gives nonzero extracted power.** The fixture satisfies the port laws, has induction
factor `1/3`, extracts the power `8 ≠ 0` and reaches the Betz limit `C_P = 16/27`. -/
lemma fixture_betz :
    betzFixture.PortLaws ∧ inductionFactor betzFixture = 1 / 3 ∧
      extractedPower betzFixture = 8 ∧ powerCoefficient betzFixture = 16 / 27 := by
  have h : betzFixture.PortLaws :=
    ⟨by norm_num [betzFixture], by norm_num [betzFixture], by norm_num [betzFixture],
      by norm_num [betzFixture]⟩
  have ha : inductionFactor betzFixture = 1 / 3 := by
    norm_num [inductionFactor, betzFixture]
  have hb := powerCoefficient_le_betz h (by norm_num [betzFixture]) (by norm_num [betzFixture])
    (by norm_num [betzFixture]) (by norm_num [betzFixture])
  exact ⟨h, ha, by norm_num [extractedPower, betzFixture], hb.2.2.2.mpr ha⟩

/-- **`U∞ = 0` is not a valid normalization.** At zero freestream speed the normalization
`ρ A U∞³ / 2` vanishes, so no coefficient normalizes a nonzero power `P`: there is no `C` with
`P = C ρ A U∞³ / 2`. -/
lemma fixture_zeroFreestream (ρ A : ℝ) {P : ℝ} (hP : P ≠ 0) :
    powerNormalization ρ A 0 = 0 ∧ ¬ ∃ C : ℝ, P = C * powerNormalization ρ A 0 := by
  have h0 : powerNormalization ρ A 0 = 0 := by simp [powerNormalization]
  refine ⟨h0, ?_⟩
  rintro ⟨C, hC⟩
  rw [h0, mul_zero] at hC
  exact hP hC

/-- **Without extraction the disk speed is not determined.** With `U_w = U∞` the port laws hold
with zero force for a disk speed other than `(U∞ + U_w) / 2`, so the hypothesis `U_w ≠ U∞` of
`uDisk_eq` cannot be dropped. -/
lemma fixture_noExtraction :
    ∃ d : ActuatorDisk, d.PortLaws ∧ 0 < d.ρ ∧ 0 < d.A ∧ 0 < d.uInf ∧ d.uWake = d.uInf ∧
      d.uDisk ≠ (d.uInf + d.uWake) / 2 := by
  refine ⟨{ ρ := 1, A := 1, uInf := 2, uDisk := 1, uWake := 2, pAmb := 0,
            pUp := 3 / 2, pDown := 3 / 2, force := 0 },
    ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- The disk state built from the induction factor `a = 1/5` at `ρ = A = 1`, `U∞ = 5` satisfies
the port laws, its induction factor is `1/5`, and its power coefficient `4 · (1/5) · (4/5)² =
64/125` is below the Betz limit `16/27`, as `powerCoefficient_le_betz` requires. -/
example :
    (ActuatorDisk.ofInduction 1 1 5 0 (1 / 5)).PortLaws ∧
      inductionFactor (ActuatorDisk.ofInduction 1 1 5 0 (1 / 5)) = 1 / 5 ∧
      powerCoefficient (ActuatorDisk.ofInduction 1 1 5 0 (1 / 5)) = 64 / 125 ∧
      powerCoefficient (ActuatorDisk.ofInduction 1 1 5 0 (1 / 5)) ≤ 16 / 27 := by
  obtain ⟨hlaws, hind, hcp⟩ := ofInduction_spec 1 1 5 0 (1 / 5)
  have hcp' := hcp (by norm_num) (by norm_num) (by norm_num)
  have hle := (powerCoefficient_le_betz hlaws (by simp [ActuatorDisk.ofInduction])
    (by simp [ActuatorDisk.ofInduction]) (by norm_num [ActuatorDisk.ofInduction])
    (by norm_num [ActuatorDisk.ofInduction])).2.2.1
  refine ⟨hlaws, hind (by norm_num), by rw [hcp']; norm_num, hle⟩

/-! ## D. The hovering rotor -/

/-- The hover fixture: `ρ = 1`, `A = 2`, still air, induced velocity `3`, far wake `6`, gauge
pressures `p∞ = 0`, `p⁺ = -9/2`, `p⁻ = 27/2`, and the force `-36` of the fluid on the disk (rotor
thrust `36`, against the flow). -/
noncomputable def hoverFixture : ActuatorDisk where
  ρ := 1
  A := 2
  uInf := 0
  uDisk := 3
  uWake := 6
  pAmb := 0
  pUp := -9 / 2
  pDown := 27 / 2
  force := -36

/-- **Nonzero hover thrust and power.** The fixture satisfies the port laws; its thrust is
`36 = 2 ρ A v_i²`, its induced velocity is `3 = √(36 / (2 ρ A))` and its induced power is
`108 = 36 · 3`. -/
lemma fixture_hover :
    hoverFixture.PortLaws ∧
      (36 : ℝ) = 2 * hoverFixture.ρ * hoverFixture.A * hoverFixture.uDisk ^ 2 ∧
      hoverFixture.uDisk = Real.sqrt (36 / (2 * hoverFixture.ρ * hoverFixture.A)) ∧
      inducedPower hoverFixture = 108 := by
  have hPL : hoverFixture.PortLaws := ⟨by norm_num [hoverFixture],
    by norm_num [hoverFixture], by norm_num [hoverFixture], by norm_num [hoverFixture]⟩
  have hρ : (0:ℝ) < hoverFixture.ρ := by norm_num [hoverFixture]
  have hA : (0:ℝ) < hoverFixture.A := by norm_num [hoverFixture]
  have h0 : hoverFixture.uInf = 0 := rfl
  have hT : hoverFixture.force = -(36:ℝ) := rfl
  have hTpos : (0:ℝ) < 36 := by norm_num
  have hT2 := hover_thrust_eq hPL hρ hA h0 hT hTpos
  have hpow : (0:ℝ) < 36 * hoverFixture.uDisk := by norm_num [hoverFixture]
  have hvi := hover_inducedVelocity_eq hPL hρ hA h0 hT hTpos hpow
  have hP := (hover_power_eq hPL hρ hA h0 hT hTpos hpow).1
  have hP108 : inducedPower hoverFixture = 108 := by
    have h3 : hoverFixture.uDisk = 3 := rfl
    rw [h3] at hP
    norm_num at hP
    exact hP
  exact ⟨hPL, hT2, hvi, hP108⟩

/-- **The freestream normalization is undefined in hover.** At `U∞ = 0` the normalization
`ρ A U∞³ / 2` of the wind-extraction power coefficient vanishes, so no coefficient `C` gives the
fixture's induced power `108` as `C ρ A U∞³ / 2`. -/
lemma fixture_hoverNoCoefficient :
    powerNormalization hoverFixture.ρ hoverFixture.A hoverFixture.uInf = 0 ∧
      ¬ ∃ C : ℝ, inducedPower hoverFixture =
        C * powerNormalization hoverFixture.ρ hoverFixture.A hoverFixture.uInf := by
  have hN : powerNormalization hoverFixture.ρ hoverFixture.A hoverFixture.uInf = 0 := by
    norm_num [powerNormalization, hoverFixture]
  refine ⟨hN, ?_⟩
  rintro ⟨C, hC⟩
  have hP : inducedPower hoverFixture = 108 := by
    norm_num [inducedPower, hoverFixture]
  rw [hP, hN, mul_zero] at hC
  norm_num at hC

/-- **The powered hypothesis cannot be dropped.** Reversing every speed of the hover fixture keeps
the port laws, the still air and the rotor thrust `36`, but the reversed state is not powered: its
thrust does the negative work `36 · (-3) = -108` on the stream, and its induced velocity `-3` is
not `√(36 / (2 ρ A)) = 3`. -/
lemma fixture_hoverReversed :
    ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk).PortLaws ∧
      36 * ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk).uDisk = -108 ∧
      ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk).uDisk ≠
        Real.sqrt (36 / (2 * hoverFixture.ρ * hoverFixture.A)) := by
  have hPL : ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk).PortLaws :=
    ⟨by norm_num [hoverFixture], by norm_num [hoverFixture],
      by norm_num [hoverFixture], by norm_num [hoverFixture]⟩
  have hW : (36:ℝ) * ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk).uDisk
      = -108 := by
    norm_num [hoverFixture]
  have hne : ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk).uDisk ≠
      Real.sqrt (36 / (2 * hoverFixture.ρ * hoverFixture.A)) := by
    have h9 : (36:ℝ) / (2 * hoverFixture.ρ * hoverFixture.A) = 9 := by
      norm_num [hoverFixture]
    have h3 : Real.sqrt (9:ℝ) = 3 := by
      rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hd : ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk).uDisk = -3 := rfl
    rw [hd, h9, h3]
    norm_num
  exact ⟨hPL, hW, hne⟩

/-- The energy balance needs no powered hypothesis: the reversed fixture state, which
`hover_power_eq` excludes, has the induced power `36 · (-3) = -108`, the negative of its extracted
power. -/
example :
    inducedPower ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk) = -108 ∧
      inducedPower ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk) =
        -extractedPower ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk) := by
  have hT : ({ hoverFixture with uDisk := -3, uWake := -6 } : ActuatorDisk).force = -(36:ℝ) := rfl
  obtain ⟨hE, hP, -⟩ := inducedPower_eq fixture_hoverReversed.1 hT
  refine ⟨?_, hE⟩
  rw [hP]
  norm_num [hoverFixture]

/-- A still-air disk with no force: induced velocity `3`, far wake `0`, gauge pressures
`p⁺ = p⁻ = -9/2`. -/
noncomputable def zeroThrustFixture : ActuatorDisk :=
  { hoverFixture with uWake := 0, pDown := -9 / 2, force := 0 }

/-- The energy balance also covers zero thrust, outside `hover_power_eq`: the zero-thrust state
satisfies the port laws and its induced power is `0 · 3 = 0`. Its far wake `0` is not `2 · 3`, so
the nonzero-force hypothesis of `hover_uWake_eq` cannot be dropped either. -/
example :
    zeroThrustFixture.PortLaws ∧ inducedPower zeroThrustFixture = 0 ∧
      zeroThrustFixture.uWake ≠ 2 * zeroThrustFixture.uDisk := by
  have hPL : zeroThrustFixture.PortLaws :=
    ⟨by norm_num [zeroThrustFixture, hoverFixture], by norm_num [zeroThrustFixture, hoverFixture],
      by norm_num [zeroThrustFixture, hoverFixture], by norm_num [zeroThrustFixture, hoverFixture]⟩
  have hT : zeroThrustFixture.force = -(0:ℝ) := by norm_num [zeroThrustFixture]
  refine ⟨hPL, ?_, by norm_num [zeroThrustFixture, hoverFixture]⟩
  rw [(inducedPower_eq hPL hT).2.1, zero_mul]

end PhyslibExtTest.FluidDynamics.RotorPorts
