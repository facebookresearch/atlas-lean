/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.PropulsionPorts
import PhyslibExt.EarthScience.ConservativeForceWork
import PhyslibExt.EarthScience.NewtonianEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Electric propulsion: ideal ion-thruster energy and thrust ports

## i. Overview

An ideal gridded ion thruster emits a monoenergetic beam of a single charge state: every ion has
the mass `m_i > 0` and the charge `q_i > 0`, starts at rest and falls through the beam voltage
`V_b > 0`, the drop `φ(start) - φ(exit)` of the electrostatic potential `φ`. Under Newton's law in
the field `-∇φ`, the power port of the kinetic energy, `EarthScience.hasDerivAt_kinetic_energy`,
and the work of the conservative force with the potential energy `q_i φ`,
`EarthScience.conservative_force_work_eq_potential_decrease_of_hasFDerivAt`, give the kinetic
energy `m_i v² / 2 = q_i V_b` at the exit, so the exhaust speed is `v_e = √(2 q_i V_b / m_i)`; this
identity needs only `m_i > 0`. A beam current `I_b > 0` carries `I_b / q_i` ions per unit time,
hence the mass flow `ṁ = I_b m_i / q_i`; a molar flow needs the Avogadro constant `N_A`,
`ṁ = (I_b / (z F)) M` with the Faraday constant `F = e N_A`, and putting the molar mass in place of
the ion mass multiplies the mass flow by `N_A`. The beam carries the kinetic power
`ṁ v_e² / 2 = I_b V_b`, the beam power `P_beam`.

With the divergence factor `γ_div ∈ [0, 1]` (the mean axial cosine of the ion velocities) the
thrust is `T = ṁ v_e γ_div`: in the separate-flow thrust of `PropulsionPorts` the thruster is a
pressure-matched rocket whose exhaust carries `ṁ` at the axial velocity `γ_div v_e`, so its
effective exhaust velocity is `γ_div v_e` and its specific impulse `γ_div v_e / g0`. For an input
power `P_in > 0` with `P_beam ≤ P_in`, the thrust efficiency is
`T² / (2 ṁ P_in) = (P_beam / P_in) γ_div² ≤ 1`. Zero beam current gives `ṁ = 0`, and the
efficiency denominator vanishes.

Model inputs: the monoenergetic beam of a single charge state, of any charge number (`q_i` is any
positive charge, such as `z e`), with ions starting at rest, the beam mass flow as the only
propellant flow, the divergence factor, and `P_in` as the electrical input power. Non-goals: no
plasma, discharge or neutral-loss model (the losses `P_in - P_beam` are not modeled), no mixed
charge-state populations (such as singly and doubly charged ions in one beam), no space-charge
limit, and no empirical adequacy or system safety claim.

## ii. Key results

- `PhyslibExt.Mechanics.ElectricPropulsion.ion_exitSpeed_of_workEnergy`: the exit kinetic energy
  `q_i V_b` and speed `v_e` from the work-energy identities.
- `PhyslibExt.Mechanics.ElectricPropulsion.beamMassFlow_of_current`, `beamMassFlow_molar`: the
  beam mass flow from the ion flow, and the molar conversion.
- `PhyslibExt.Mechanics.ElectricPropulsion.beam_energy_port`: `m_i v_e² / 2 = q_i V_b` and
  `ṁ v_e² / 2 = P_beam`.
- `PhyslibExt.Mechanics.ElectricPropulsion.ionThrust_eq_separateFlowThrust`: the thrust port in
  the separate-flow form, the effective exhaust velocity and the specific impulse.
- `PhyslibExt.Mechanics.ElectricPropulsion.thrustEfficiency_eq_le_one`: the efficiency identity
  and its bound.
- `PhyslibExt.Mechanics.ElectricPropulsion.zeroFlow_invalid`: zero beam current leaves the
  efficiency denominator zero.

A nonzero beam with `γ_div < 1` and a uniform accelerating gap are in
`PhyslibExtTest.Mechanics.ElectricPropulsionTest`.

## iii. Table of contents

- A. Beam quantities
- B. Exhaust speed from work and energy
- C. Mass flow, energy port and thrust port
- D. Thrust efficiency
- E. Zero flow

## iv. References

- D. M. Goebel and I. Katz, *Fundamentals of Electric Propulsion: Ion and Hall Thrusters*, Wiley,
  2008, chapter 2 (thrust, beam current and power, thrust efficiency, divergence factor).
- R. G. Jahn, *Physics of Electric Propulsion*, McGraw-Hill, 1968 (electrostatic acceleration).
- `PhyslibExt.EarthScience.NewtonianEnergy` and `PhyslibExt.EarthScience.ConservativeForceWork`:
  the kinetic-energy derivative and the work of a conservative force reused here.
- `PhyslibExt.Mechanics.PropulsionPorts`: the separate-flow thrust and the specific impulse reused
  here; the test module drives the work-energy lemma along the constant-force trajectory of
  `PhyslibExt.Mechanics.PowerPorts`.
-/

@[expose] public section

namespace PhyslibExt.Mechanics.ElectricPropulsion

open Set MeasureTheory PhyslibExt.Mechanics.PropulsionPorts

/-! ## A. Beam quantities -/

/-- The exhaust speed `v_e = √(2 q_i V_b / m_i)` of an ion of mass `m_i` and charge `q_i` that
starts at rest and falls through the beam voltage `V_b`. -/
noncomputable def ionExhaustSpeed (mi qi Vb : ℝ) : ℝ := Real.sqrt (2 * qi * Vb / mi)

/-- The beam mass flow `ṁ = I_b m_i / q_i`: the current `I_b` carries `I_b / q_i` ions of mass
`m_i` per unit time. -/
noncomputable def beamMassFlow (mi qi Ib : ℝ) : ℝ := Ib * mi / qi

/-- The beam power `P_beam = I_b V_b`. -/
def beamPower (Vb Ib : ℝ) : ℝ := Ib * Vb

/-- The thrust `T = ṁ v_e γ_div` of the beam with the divergence factor `γ_div`. -/
noncomputable def ionThrust (mi qi Vb Ib γ : ℝ) : ℝ :=
  beamMassFlow mi qi Ib * ionExhaustSpeed mi qi Vb * γ

/-- The thrust efficiency `η_T = T² / (2 ṁ P_in)` of the thrust `T` at the mass flow `ṁ` and the
input power `P_in`. -/
noncomputable def thrustEfficiency (T mdot Pin : ℝ) : ℝ := T ^ 2 / (2 * mdot * Pin)

/-! ## B. Exhaust speed from work and energy -/

/-- **Exhaust speed from work and energy.** A particle of mass `m_i > 0` and charge `q_i` moves on
`[0, t₁]`, `t₁ ≥ 0`, under Newton's law `m_i a = -q_i ∇φ(γ)` in the field of an electrostatic
potential `φ` with continuous gradient `∇φ`. If it starts at rest and the potential drops by
`V_b = φ(γ 0) - φ(γ t₁)`, then at `t₁` its kinetic energy is `m_i ‖v‖² / 2 = q_i V_b` and its speed
is `v_e = √(2 q_i V_b / m_i)`. For a positive ion falling through the beam voltage, `q_i > 0` and
`V_b > 0`; the identity holds for either sign of the charge. -/
lemma ion_exitSpeed_of_workEnergy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mi qi Vb t₁ : ℝ} (hmi : 0 < mi) (ht₁ : 0 ≤ t₁)
    {φ : E → ℝ} {gradφ : E → E} (hφ : ∀ x, HasFDerivAt φ (innerSL ℝ (gradφ x)) x)
    (hgrad : Continuous gradφ) {γ v a : ℝ → E}
    (hγ : ∀ t ∈ Icc 0 t₁, HasDerivAt γ (v t) t) (hv : ∀ t ∈ Icc 0 t₁, HasDerivAt v (a t) t)
    (hnewton : ∀ t ∈ Icc 0 t₁, mi • a t = -(qi • gradφ (γ t)))
    (hrest : v 0 = 0) (hdrop : φ (γ 0) - φ (γ t₁) = Vb) :
    mi * ‖v t₁‖ ^ 2 / 2 = qi * Vb ∧ ‖v t₁‖ = ionExhaustSpeed mi qi Vb := by
  have hI : uIcc 0 t₁ = Icc 0 t₁ := uIcc_of_le ht₁
  have hU : ∀ x, HasFDerivAt (fun y => qi * φ y) (innerSL ℝ (qi • gradφ x)) x := fun x =>
    ((hφ x).const_mul qi).congr_fderiv (by ext y; simp)
  have hγc : ContinuousOn γ (Icc 0 t₁) := fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Icc 0 t₁) := fun t ht => (hv t ht).continuousAt.continuousWithinAt
  have hpc : ContinuousOn (fun t => inner ℝ (-(qi • gradφ (γ t))) (v t)) (Icc 0 t₁) :=
    ((hgrad.comp_continuousOn hγc).const_smul qi).neg.inner hvc
  have hint : IntervalIntegrable (fun t => inner ℝ (-(qi • gradφ (γ t))) (v t)) volume 0 t₁ := by
    apply ContinuousOn.intervalIntegrable
    rwa [hI]
  have hwork := EarthScience.conservative_force_work_eq_potential_decrease_of_hasFDerivAt
    (U := fun y => qi * φ y) (g := fun x => qi • gradφ x) (F := fun x => -(qi • gradφ x))
    (fun x => rfl) hU (fun t ht => hγ t (hI ▸ ht)) hint
  have hpow : ∀ t ∈ uIcc 0 t₁, HasDerivAt (fun s => mi * ‖v s‖ ^ 2 / 2)
      (inner ℝ (-(qi • gradφ (γ t))) (v t)) t := by
    intro t ht
    rw [hI] at ht
    have h := EarthScience.hasDerivAt_kinetic_energy (m := mi) (hv t ht)
    rwa [hnewton t ht] at h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hpow hint
  rw [hwork, hrest, norm_zero] at hftc
  have hqV : qi * Vb = qi * φ (γ 0) - qi * φ (γ t₁) := by
    rw [← hdrop]
    ring
  have hK : mi * ‖v t₁‖ ^ 2 / 2 = qi * Vb := by
    norm_num at hftc
    linarith
  refine ⟨hK, ?_⟩
  have hsq : ‖v t₁‖ ^ 2 = 2 * qi * Vb / mi := by
    field_simp
    linarith
  rw [ionExhaustSpeed, ← hsq, Real.sqrt_sq (norm_nonneg _)]

/-! ## C. Mass flow, energy port and thrust port -/

/-- **Mass flow from the current.** For a single charge state `q_i > 0`, a beam whose current is
carried by `ṅ` ions per unit time, `I_b = ṅ q_i`, has the mass flow `I_b m_i / q_i = ṅ m_i`. -/
lemma beamMassFlow_of_current {mi qi Ib ndot : ℝ} (hqi : 0 < qi) (hI : Ib = ndot * qi) :
    beamMassFlow mi qi Ib = ndot * mi := by
  rw [beamMassFlow, hI]
  field_simp

/-- **Molar flow needs the Avogadro constant.** For ions of molar mass `M` and charge number
`z > 0`, with the elementary charge `e > 0` and the Avogadro constant `N_A > 0`, the ion mass is
`M / N_A` and the charge `z e`: the beam mass flow is the molar flow `I_b / (z F)`, `F = e N_A`,
times `M`, and putting the molar mass in place of the ion mass multiplies the mass flow by the
factor `N_A`. -/
lemma beamMassFlow_molar {M e NA z Ib : ℝ} (he : 0 < e) (hNA : 0 < NA) (hz : 0 < z) :
    beamMassFlow (M / NA) (z * e) Ib = Ib / (z * (e * NA)) * M ∧
      beamMassFlow M (z * e) Ib = NA * beamMassFlow (M / NA) (z * e) Ib := by
  have he0 : e ≠ 0 := he.ne'
  have hNA0 : NA ≠ 0 := hNA.ne'
  have hz0 : z ≠ 0 := hz.ne'
  unfold beamMassFlow
  constructor
  · field_simp
  · field_simp

/-- **Energy port.** For `m_i, q_i, V_b > 0` each ion leaves with the kinetic energy
`m_i v_e² / 2 = q_i V_b`, and a beam of current `I_b` carries the kinetic power
`ṁ v_e² / 2 = I_b V_b = P_beam`. -/
lemma beam_energy_port {mi qi Vb : ℝ} (hmi : 0 < mi) (hqi : 0 < qi) (hVb : 0 < Vb) (Ib : ℝ) :
    mi * ionExhaustSpeed mi qi Vb ^ 2 / 2 = qi * Vb ∧
      beamMassFlow mi qi Ib * ionExhaustSpeed mi qi Vb ^ 2 / 2 = beamPower Vb Ib := by
  have hsq : ionExhaustSpeed mi qi Vb ^ 2 = 2 * qi * Vb / mi := by
    rw [ionExhaustSpeed, Real.sq_sqrt (by positivity)]
  rw [hsq, beamMassFlow, beamPower]
  constructor
  · field_simp
  · field_simp

/-- **Thrust port.** For `m_i, q_i, I_b > 0` the thrust `T = ṁ v_e γ_div` is the separate-flow
thrust of `PropulsionPorts` of a pressure-matched rocket (no inlet stream, no capture area, exhaust
pressure equal to the ambient `p`) whose exhaust carries `ṁ` at the axial velocity `v_e γ_div`,
whatever the unused inlet data and the exhaust area. Its effective exhaust velocity is
`v_e γ_div` and its specific impulse `v_e γ_div / g0`. -/
lemma ionThrust_eq_separateFlowThrust {mi qi Ib : ℝ} (hmi : 0 < mi) (hqi : 0 < qi)
    (hIb : 0 < Ib) (Vb γ vIn pIn p AE g0 : ℝ) :
    ionThrust mi qi Vb Ib γ = separateFlowThrust 0 vIn pIn 0 (beamMassFlow mi qi Ib)
        (ionExhaustSpeed mi qi Vb * γ) p AE p ∧
      effectiveExhaustVelocity (ionThrust mi qi Vb Ib γ) (beamMassFlow mi qi Ib) =
        ionExhaustSpeed mi qi Vb * γ ∧
      specificImpulse (ionThrust mi qi Vb Ib γ) (beamMassFlow mi qi Ib) g0 =
        ionExhaustSpeed mi qi Vb * γ / g0 := by
  have hm : beamMassFlow mi qi Ib ≠ 0 := by
    rw [beamMassFlow]
    positivity
  have hc : effectiveExhaustVelocity (ionThrust mi qi Vb Ib γ) (beamMassFlow mi qi Ib) =
      ionExhaustSpeed mi qi Vb * γ := by
    rw [effectiveExhaustVelocity, ionThrust]
    field_simp
  refine ⟨?_, hc, ?_⟩
  · rw [ionThrust, separateFlowThrust]
    ring
  · rw [specificImpulse_totalFlow_eq, hc]

/-! ## D. Thrust efficiency -/

/-- **Thrust efficiency.** For `m_i, q_i, V_b, I_b, P_in > 0`, `γ_div ∈ [0, 1]` and
`P_beam = I_b V_b ≤ P_in`, the thrust efficiency of the beam is
`T² / (2 ṁ P_in) = (P_beam / P_in) γ_div²`, and this is at most `1`. -/
lemma thrustEfficiency_eq_le_one {mi qi Vb Ib Pin γ : ℝ} (hmi : 0 < mi) (hqi : 0 < qi)
    (hVb : 0 < Vb) (hIb : 0 < Ib) (hPin : 0 < Pin) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hP : beamPower Vb Ib ≤ Pin) :
    thrustEfficiency (ionThrust mi qi Vb Ib γ) (beamMassFlow mi qi Ib) Pin =
        beamPower Vb Ib / Pin * γ ^ 2 ∧
      beamPower Vb Ib / Pin * γ ^ 2 ≤ 1 := by
  have hsq : ionExhaustSpeed mi qi Vb ^ 2 = 2 * qi * Vb / mi := by
    rw [ionExhaustSpeed, Real.sq_sqrt (by positivity)]
  constructor
  · rw [thrustEfficiency, ionThrust, mul_pow, mul_pow, hsq, beamMassFlow, beamPower]
    field_simp
  · have h1 : beamPower Vb Ib / Pin ≤ 1 := (div_le_one hPin).mpr hP
    have h2 : 0 ≤ beamPower Vb Ib / Pin := div_nonneg (by rw [beamPower]; positivity) hPin.le
    have h3 : γ ^ 2 ≤ 1 := pow_le_one₀ hγ0 hγ1
    nlinarith [sq_nonneg γ]

/-! ## E. Zero flow -/

/-- **Zero flow leaves the efficiency undefined.** For `m_i, q_i, V_b > 0` and no beam current
the beam mass flow is `0`, so the efficiency denominator `2 ṁ P_in` vanishes (Lean's `x / 0 = 0`
then makes `T² / (2 ṁ P_in)` equal `0`, which is not a physical efficiency), while each ion would
still leave at `v_e > 0`. -/
lemma zeroFlow_invalid {mi qi Vb : ℝ} (hmi : 0 < mi) (hqi : 0 < qi) (hVb : 0 < Vb) (Pin : ℝ) :
    beamMassFlow mi qi 0 = 0 ∧ 2 * beamMassFlow mi qi 0 * Pin = 0 ∧
      0 < ionExhaustSpeed mi qi Vb := by
  have h0 : beamMassFlow mi qi 0 = 0 := by simp [beamMassFlow]
  refine ⟨h0, by rw [h0]; ring, ?_⟩
  rw [ionExhaustSpeed]
  positivity

end PhyslibExt.Mechanics.ElectricPropulsion
