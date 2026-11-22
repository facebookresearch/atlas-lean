/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import PhyslibExt.Mechanics.PowerPorts
public import PhyslibExt.ContinuumMechanics.ControlVolumes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variable-mass propulsion: velocity increment, parcel consistency, stationary thrust, staging

Reduced collinear model of an ideal rocket burn on `[0, tb]`: positive mass `m`, velocity `v`,
constant exhaust speed `ve > 0` relative to the vehicle, directed backward, and the declared law
`m t * v' t = -ve * m' t` (thrust equals mass flow `-m'` times exhaust speed). Separately, the
steady momentum port balance of an engine at rest gives the separate-flow thrust with inlet, fuel
and exhaust flows and port pressures, and its exhaust velocity and specific impulses.

## i. Overview

No external force (gravity, drag) acts in this law, and it is a stated model input, not a
consequence of a fixed-mass Newtonian system. Integrating it gives the ideal rocket equation
`v tb - v 0 = ve * log (m 0 / m tb)`. For nonincreasing mass the increment is nonnegative, zero
exactly at equal end masses and positive exactly for a nonzero burn; constant mass gives no
increment. In this pressure-matched model (no pressure-thrust term) the specific impulse is
`ve / g0`, with `g0 > 0` the reference acceleration used to quote `Isp` in seconds, not
necessarily local gravity. Signs: `m' < 0` during a burn, so `v' = -ve * m' / m > 0`.

The law is consistent with an explicit momentum-conserving parcel model at one state `(m, v)`:
in a step of length `h` a parcel of mass `q h` leaves with velocity `v - ve` and the external
force `F` delivers the impulse `F h`, so `(m - q h) v_h + q h (v - ve) = m v + F h`. The step
identities hold for arbitrary real parameters whenever their denominators are nonzero: the update
`v_h` is the unique solution of the balance when the remaining mass `m - q h` is nonzero, and its
slope is exactly `(v_h - v) / h = (ve q + F) / (m - q h)` when also `h ≠ 0`. For `m > 0` both
conditions hold for every `h ≠ 0` near `0`, and the slope tends to `(ve q + F) / m` as `h → 0`; a
physical step also has `q ≥ 0` and `h > 0`. For a differentiable mass history `M` with `M t > 0`
that is burning at `t` (`M' < 0`), a forward step from `t` to `t + h`, `h > 0`, expels the actual
mass `M t - M (t + h)`, at the rate `q_h = (M t - M (t + h)) / h`: for small `h` the expelled mass
is nonnegative, the remaining mass is exactly `M (t + h)`, the step conserves momentum, `q_h`
tends to `-M'`, and the slope tends to the acceleration `a` of `M a = -ve M' + F`, the law above
when `F = 0`. A linear burning history expels mass at exactly the constant rate `-M'` in every
forward step that leaves positive mass, `0 < M (t + h)`, and for those steps the constant-flow
step is the actual parcel step, with the momentum balance; a longer step would leave no mass or
negative mass and is not a parcel step. For `m > 0`, the update with no expelled mass is the
fixed-mass constant-force velocity of `PhyslibExt.Mechanics.PowerPorts`, and ignoring the
expelled momentum gives the slope limit `(q v + F) / m` instead, wrong whenever `q (v - ve) ≠ 0`.
This is local consistency of the parcel model, not convergence of a discrete integration scheme
or an exact finite-step logarithmic law.

Sections G-I treat an engine at rest on a test stand in an inertial frame. Its control volume has
an inlet (capture) port of area `A_in` and an exhaust port of area `A_e`, normal to the engine
axis, and a fuel feed. The axis points aft, the direction of the exhaust: the port velocities
`v_in`, `v_e` are axial components relative to the engine, positive aft, so the outward unit
normals of the inlet and exhaust ports are `-1` and `+1` and the port mass flows are `ṁ_in`,
`ṁ_out ≥ 0`. The port pressures are `p_in`, `p_e`, the ambient pressure is `p_a`, the fuel enters
with the mass flow `ṁ_f` and the axial velocity `v_f`, and the thrust `T` is positive forward.
The axial momentum balance in the port form of `ControlVolumes.hasDerivAt_momentum_twoPort` (a
uniform ambient pressure has zero resultant over the closed surface) gives the axial force of the
stand on the contents as `F = T + P' - ṁ_f v_f` with
`T = ṁ_out v_e - ṁ_in v_in + (p_e - p_a) A_e - (p_in - p_a) A_in`; in a steady state with
negligible fuel feed momentum (`v_f = 0`) the stand force is the thrust, which the engine exerts
forward on the stand. For a box with equal port areas, `ControlVolumes.hasDerivAt_momentum_twoPort`
itself gives the balance from the local Cauchy momentum law: with a stationary momentum and no
axial body force, the axial traction resultant of the duct walls on the fluid is the
separate-flow thrust. The steady mass balance is `ṁ_out = ṁ_in + ṁ_f`. A rocket has no inlet
stream and no air-capture area, so `T = ṁ_f v_e + (p_e - p_a) A_e`, positive for `ṁ_f, v_e > 0`
and `p_e ≥ p_a`; an air-breather with `p_in = p_a` at its capture plane has
`T = (ṁ_in + ṁ_f) v_e - ṁ_in v_in + (p_e - p_a) A_e`, and with fuel the exhaust flow exceeds the
inlet flow, the equal-flow formula being the special case `ṁ_f = 0`. The effective exhaust
velocity is `c = T / ṁ_out`; the total-flow specific impulse is `T / (ṁ_out g0) = c / g0` and the
fuel-flow specific impulse `T / (ṁ_f g0)`, both with `specificImpulse`. They coincide for a rocket
and differ by the factor `ṁ_out / ṁ_f > 1` for an air-breather with positive inlet flow and
thrust. For an accelerating vehicle this thrust is only an adopted quasisteady engine-port law,
unless the storage term `P'` and the acceleration of the engine frame are included; it is not an
exact transient control-volume identity.

Section J treats a staged vehicle. It flies a finite sequence of burns `i = 0, …, n` in one fixed
direction, burn `i` on its own interval `[0, tb i]` with positive mass `m i`, velocity `v i` and
exhaust speed `ve i` under the law above. Between burn `i` and burn `i + 1` it jettisons the dry
mass `m i (tb i) - m (i + 1) 0 ≥ 0` with zero velocity relative to itself; momentum conservation
`m (i + 1) 0 w + (m i (tb i) - m (i + 1) 0) v = m i (tb i) v` leaves the velocity unchanged,
`w = v`, while the mass drops without any continuity across the event. Summing the burn
increments, the velocity gained over the whole sequence is
`∑ i, ve i * log (m i 0 / m i (tb i))` with stage-specific exhaust speeds, and no jettisoned mass
enters a logarithm. Counting a dry-mass drop from `m₁` to `m₂ < m₁` as propellant instead adds
`ve * log (m₁ / m₂) > 0` for `ve > 0`: it overstates the available increment. For collinear burns
the sum is a net velocity increment; for burns in different directions it would be only a scalar
burn cost, about which nothing is stated here.

## ii. Key results

- `velocity_increment_eq_log`: the ideal rocket equation from derivative data, positive mass and
  the law.
- `velocity_increment_burn_and_boundary`: for `ve > 0`, nonnegative increment, zero exactly at
  equal end masses, positive exactly for a nonzero burn.
- `specificImpulse_eq_of_law`: `Isp = ve / g0` at any burning instant.
- `velocity_increment_const_mass`: constant positive mass gives zero increment.
- `parcelVelocity`, `parcel_momentum_iff`, `parcel_slope_eq`: the parcel step, its momentum
  balance when the remaining mass is nonzero, and its exact slope when also `h ≠ 0`.
- `eventually_parcel_mass_pos`, `parcel_slope_tendsto`: for `m > 0`, the remaining mass is
  positive for every `h` near `0`, and the first-order limit of the parcel step.
- `parcel_continuum`, `parcel_continuum_linear`: for a burning mass history (`M' < 0`), the
  forward step with the actual, nonnegative expelled mass, its momentum balance and its continuum
  limit; a linear burning history expels mass at exactly the constant rate `-M'` in every forward
  step that leaves positive mass, where the constant-flow step is the actual parcel step.
- `parcelVelocity_zero_flow`: for `m > 0` and no expelled mass, the fixed-mass constant-force
  velocity.
- `parcel_accel_pos`, `naive_slope_tendsto`, `naive_limit_ne`: for `m > 0`, a positive flow at a
  positive exhaust speed accelerates the vehicle, and ignoring the expelled momentum gives the
  wrong derivative whenever `q (v - ve) ≠ 0`.
- `separateFlowThrust`, `standForce_eq_separateFlowThrust_add`, `standForce_eq_separateFlowThrust`:
  the thrust expression and the stand force from the port balance, with the storage and feed
  terms, and the steady thrust.
- `wallForce_eq_separateFlowThrust`: the box balance of `ControlVolumes` gives the thrust with
  equal port areas.
- `separateFlowThrust_rocket`, `separateFlowThrust_rocket_pos`, `separateFlowThrust_airBreather`,
  `airBreather_exhaustFlow`: the rocket and air-breather instances.
- `effectiveExhaustVelocity`, `specificImpulse_totalFlow_eq`, `specificImpulse_fuelFlow_eq`,
  `specificImpulse_rocket_flows_eq`, `specificImpulse_totalFlow_lt_fuelFlow`,
  `effectiveExhaustVelocity_rocket_matched`: the exhaust velocity and the total-flow and
  fuel-flow specific impulses.
- `jettison_velocity_eq`: a zero-relative-velocity jettison conserves momentum exactly when the
  velocity is unchanged.
- `staged_velocity_increment`: the velocity gained over burns separated by such jettisons is the
  sum of the burn increments, with stage-specific exhaust speeds and the jettisoned masses outside
  every logarithm.
- `jettison_as_propellant_overstates`: counting a dry-mass drop as propellant overstates the
  increment.

## iii. Table of contents

- A. Integrated velocity increment
- B. Specific impulse
- C. Constant mass
- D. One parcel step
- E. The first-order limit and the continuum model
- F. Validation
- G. Separate-flow thrust from the port balance
- H. Rocket and air-breather
- I. Effective exhaust velocity and specific impulse
- J. Staged burns and dry-mass jettison

## iv. References

- G. P. Sutton and O. Biblarz, *Rocket Propulsion Elements*, 9th edition, chapters 2 to 4
  (thrust with the pressure term, specific impulse, effective exhaust velocity, ideal rocket
  equation; multistage vehicles).
- P. G. Hill and C. R. Peterson, *Mechanics and Thermodynamics of Propulsion*, 2nd edition,
  Addison-Wesley (1992), chapters 6 and 11 (thrust of air-breathing and rocket engines).
- H. D. Curtis, *Orbital Mechanics for Engineering Students*, rocket vehicle dynamics chapter
  (staging).
- D. Kleppner and R. Kolenkow, *An Introduction to Mechanics*, 2nd edition, chapter 4 (momentum
  of a system with a varying mass; the rocket).
- `PhyslibExt.Mechanics.PowerPorts`: the fixed-mass constant-force velocity.
- `ControlVolumes.hasDerivAt_momentum_twoPort` (`PhyslibExt.ContinuumMechanics.ControlVolumes`):
  the two-port momentum balance.
-/

@[expose] public section

namespace PhyslibExt.Mechanics.PropulsionPorts

open Set

/-! ## A. Integrated velocity increment -/

/-- Ideal rocket equation from the reduced variable-mass law. For mass `m` and velocity `v`
with derivatives `m'`, `v'` on `[0, tb]`, positive mass and the law `m * v' = -ve * m'` on
`[0, tb]`, the velocity increment is `ve * log (m 0 / m tb)`. Neither the sign of `ve` nor
continuity of the derivatives is needed, so the identity covers the model's `C¹` histories with
`ve > 0` as a special case. -/
lemma velocity_increment_eq_log {m v m' v' : ℝ → ℝ} {ve tb : ℝ} (htb : 0 ≤ tb)
    (hm : ∀ t ∈ Icc 0 tb, HasDerivAt m (m' t) t) (hv : ∀ t ∈ Icc 0 tb, HasDerivAt v (v' t) t)
    (hpos : ∀ t ∈ Icc 0 tb, 0 < m t) (hlaw : ∀ t ∈ Icc 0 tb, m t * v' t = -ve * m' t) :
    v tb - v 0 = ve * Real.log (m 0 / m tb) := by
  have h0mem : (0 : ℝ) ∈ Icc 0 tb := ⟨le_refl 0, htb⟩
  have htbmem : tb ∈ Icc 0 tb := ⟨htb, le_refl tb⟩
  have hm0_ne : m 0 ≠ 0 := ne_of_gt (hpos 0 h0mem)
  have hmtb_ne : m tb ≠ 0 := ne_of_gt (hpos tb htbmem)
  have hlog : ∀ t ∈ Icc 0 tb, HasDerivAt (fun t => Real.log (m t)) (m' t / m t) t :=
    fun t ht => (hm t ht).log (ne_of_gt (hpos t ht))
  have hder0 : ∀ t ∈ Icc 0 tb, v' t + ve * (m' t / m t) = 0 := by
    intro t ht
    have hne : m t ≠ 0 := ne_of_gt (hpos t ht)
    have h1 := hlaw t ht
    field_simp
    linear_combination h1
  have hF : ∀ t ∈ Icc 0 tb,
      HasDerivAt (fun t => v t + ve * Real.log (m t)) 0 t := by
    intro t ht
    have h := (hv t ht).fun_add (HasDerivAt.const_mul ve (hlog t ht))
    simpa [hder0 t ht] using h
  have huIcc : uIcc 0 tb = Icc 0 tb := uIcc_of_le htb
  have hderiv : ∀ x ∈ uIcc 0 tb,
      HasDerivAt (fun t => v t + ve * Real.log (m t)) ((fun _ => (0 : ℝ)) x) x := by
    rw [huIcc]
    simpa using hF
  have hint : IntervalIntegrable (fun _ => (0 : ℝ)) MeasureTheory.volume 0 tb :=
    intervalIntegrable_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hzero : (v tb + ve * Real.log (m tb)) - (v 0 + ve * Real.log (m 0)) = 0 := by
    simpa using hFTC.symm
  have hlogdiv := Real.log_div hm0_ne hmtb_ne
  rw [hlogdiv]
  linear_combination hzero

/-- Nonincreasing mass admits both cases: for `ve > 0` the increment is nonnegative, zero exactly
when the end masses are equal (no net burn), and positive exactly when mass was expelled. No
continuity of the derivatives is needed. -/
lemma velocity_increment_burn_and_boundary {m v m' v' : ℝ → ℝ} {ve tb : ℝ} (htb : 0 ≤ tb)
    (hve : 0 < ve) (hm : ∀ t ∈ Icc 0 tb, HasDerivAt m (m' t) t)
    (hv : ∀ t ∈ Icc 0 tb, HasDerivAt v (v' t) t) (hpos : ∀ t ∈ Icc 0 tb, 0 < m t)
    (hlaw : ∀ t ∈ Icc 0 tb, m t * v' t = -ve * m' t) (hanti : AntitoneOn m (Icc 0 tb)) :
    0 ≤ v tb - v 0 ∧ (v tb - v 0 = 0 ↔ m tb = m 0) ∧ (0 < v tb - v 0 ↔ m tb < m 0) := by
  have hmain := velocity_increment_eq_log htb hm hv hpos hlaw
  have h0mem : (0 : ℝ) ∈ Icc 0 tb := ⟨le_refl 0, htb⟩
  have htbmem : tb ∈ Icc 0 tb := ⟨htb, le_refl tb⟩
  have hm0_pos : 0 < m 0 := hpos 0 h0mem
  have hmtb_pos : 0 < m tb := hpos tb htbmem
  have hm0_ne : m 0 ≠ 0 := ne_of_gt hm0_pos
  have hmtb_ne : m tb ≠ 0 := ne_of_gt hmtb_pos
  have hle : m tb ≤ m 0 := hanti h0mem htbmem htb
  have hr_pos : 0 < m 0 / m tb := div_pos hm0_pos hmtb_pos
  have hr_nonneg : 0 ≤ m 0 / m tb := le_of_lt hr_pos
  have h1le : 1 ≤ m 0 / m tb := by
    rw [le_div_iff₀ hmtb_pos, one_mul]
    exact hle
  have hlog_nonneg : 0 ≤ Real.log (m 0 / m tb) := Real.log_nonneg h1le
  have hve_ne : ve ≠ 0 := ne_of_gt hve
  have hinc_nonneg : 0 ≤ v tb - v 0 := by
    rw [hmain]
    exact mul_nonneg (le_of_lt hve) hlog_nonneg
  refine ⟨hinc_nonneg, ?_, ?_⟩
  · rw [hmain]
    constructor
    · intro h
      have hlog0 : Real.log (m 0 / m tb) = 0 := by
        rcases (mul_eq_zero.mp h) with hve0 | hlog0
        · exact absurd hve0 hve_ne
        · exact hlog0
      have hr1 : m 0 / m tb = 1 := by
        rcases (Real.log_eq_zero.mp hlog0) with h0 | h1 | hneg
        · exact absurd h0 hr_pos.ne'
        · exact h1
        · exfalso
          linarith [hr_pos, hneg]
      have heq : m 0 = m tb := (div_eq_one_iff_eq hmtb_ne).mp hr1
      exact heq.symm
    · intro h
      rw [h, div_self hm0_ne, Real.log_one, mul_zero]
  · rw [hmain, mul_pos_iff_of_pos_left hve, Real.log_pos_iff hr_nonneg,
      lt_div_iff₀ hmtb_pos, one_mul]

/-! ## B. Specific impulse -/

/-- Specific impulse `T / (mdot * g0)` of thrust `T` at propellant mass flow `mdot`, quoted
with the reference acceleration `g0` (a fixed standard value, not necessarily local
gravity). -/
noncomputable def specificImpulse (T mdot g0 : ℝ) : ℝ :=
  T / (mdot * g0)

/-- In the pressure-matched model the thrust is the momentum rate `m * v' = (-m') * ve`, so at
any burning instant (`m' t < 0`) the specific impulse is `ve / g0`. -/
lemma specificImpulse_eq_of_law {m v' m' : ℝ → ℝ} {ve g0 t : ℝ} (hg0 : 0 < g0)
    (hburn : m' t < 0) (hlaw : m t * v' t = -ve * m' t) :
    specificImpulse (m t * v' t) (-m' t) g0 = ve / g0 := by
  have hmdot_ne : -m' t ≠ 0 := ne_of_gt (neg_pos.mpr hburn)
  have hm'_ne : m' t ≠ 0 := ne_of_lt hburn
  have hg0_ne : g0 ≠ 0 := ne_of_gt hg0
  unfold specificImpulse
  rw [hlaw]
  field_simp

/-! ## C. Constant mass -/

/-- Boundary: with constant positive mass the law forces `v' = 0`, so the increment is zero
(`ve * log (M / M) = 0`). -/
lemma velocity_increment_const_mass {v v' : ℝ → ℝ} {M ve tb : ℝ} (htb : 0 ≤ tb) (hM : 0 < M)
    (hv : ∀ t ∈ Icc 0 tb, HasDerivAt v (v' t) t) (hlaw : ∀ t ∈ Icc 0 tb, M * v' t = -ve * 0) :
    v tb = v 0 := by
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hv0 : ∀ t ∈ Icc 0 tb, HasDerivAt v 0 t := by
    intro t ht
    have h1 := hlaw t ht
    have hzero : M * v' t = 0 := by simpa using h1
    have hv'_eq : v' t = 0 := by
      rcases mul_eq_zero.mp hzero with hM0 | hv0
      · exact absurd hM0 hM_ne
      · exact hv0
    simpa [hv'_eq] using hv t ht
  have huIcc : uIcc 0 tb = Icc 0 tb := uIcc_of_le htb
  have hderiv : ∀ x ∈ uIcc 0 tb, HasDerivAt v ((fun _ => (0 : ℝ)) x) x := by
    rw [huIcc]
    simpa using hv0
  have hint : IntervalIntegrable (fun _ => (0 : ℝ)) MeasureTheory.volume 0 tb :=
    intervalIntegrable_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hsub : v tb - v 0 = 0 := by simpa using hFTC.symm
  exact sub_eq_zero.mp hsub

open Filter Topology PhyslibExt.Mechanics.PowerPorts

/-! ## D. One parcel step -/

/-- Vehicle velocity after one parcel step of length `h` from the state `(m, v)`: the momentum
balance `(m - q h) v_h + q h (v - ve) = m v + F h` solved for `v_h`, which needs the remaining
mass `m - q h` to be nonzero. -/
noncomputable def parcelVelocity (m v q ve F h : ℝ) : ℝ :=
  (m * v + F * h - q * h * (v - ve)) / (m - q * h)

/-- When the remaining mass `m - q h` is nonzero, the update is the unique solution of the parcel
momentum balance. -/
lemma parcel_momentum_iff {m q h : ℝ} (hmh : m - q * h ≠ 0) (v ve F w : ℝ) :
    (m - q * h) * w + q * h * (v - ve) = m * v + F * h ↔ w = parcelVelocity m v q ve F h := by
  unfold parcelVelocity
  rw [eq_div_iff hmh]
  constructor <;> intro hh <;> linear_combination hh

/-- For `m > 0` and `h` small enough the remaining mass `m - q h` is positive. -/
lemma eventually_parcel_mass_pos {m : ℝ} (hm : 0 < m) (q : ℝ) : ∀ᶠ h in 𝓝 0, 0 < m - q * h := by
  have hcont : ContinuousAt (fun h : ℝ => m - q * h) 0 := by fun_prop
  have hmem : (fun h : ℝ => m - q * h) 0 ∈ Set.Ioi (0 : ℝ) := by simpa using hm
  have hnbhd := isOpen_Ioi.mem_nhds hmem
  simpa using Tendsto.eventually hcont hnbhd

/-- Exact slope of one step with `h ≠ 0` and nonzero remaining mass `m - q h`:
`(v_h - v) / h = (ve q + F) / (m - q h)`. -/
lemma parcel_slope_eq {m q h : ℝ} (hh : h ≠ 0) (hmh : m - q * h ≠ 0) (v ve F : ℝ) :
    (parcelVelocity m v q ve F h - v) / h = (ve * q + F) / (m - q * h) := by
  unfold parcelVelocity
  have hmh' : m - h * q ≠ 0 := by
    intro hc
    apply hmh
    linear_combination hc
  field_simp
  ring

/-! ## E. The first-order limit and the continuum model -/

/-- For `m > 0` the slope tends to the acceleration `(ve q + F) / m` as `h → 0`. -/
lemma parcel_slope_tendsto {m : ℝ} (hm : 0 < m) (v q ve F : ℝ) :
    Tendsto (fun h => (parcelVelocity m v q ve F h - v) / h) (𝓝[≠] 0)
      (𝓝 ((ve * q + F) / m)) := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have heq : (fun h : ℝ => (parcelVelocity m v q ve F h - v) / h)
      =ᶠ[𝓝[≠] 0] ((fun _ : ℝ => ve * q + F) / (fun h : ℝ => m - q * h)) := by
    have hpos : ∀ᶠ h in 𝓝[≠] (0 : ℝ), 0 < m - q * h :=
      Eventually.filter_mono nhdsWithin_le_nhds (eventually_parcel_mass_pos hm q)
    filter_upwards [self_mem_nhdsWithin, hpos] with h hh0 hpos
    have hh : h ≠ 0 := by simpa using hh0
    have hmh : m - q * h ≠ 0 := ne_of_gt hpos
    simp only [Pi.div_apply]
    exact parcel_slope_eq hh hmh v ve F
  have hden : Tendsto (fun h : ℝ => m - q * h) (𝓝[≠] (0 : ℝ)) (𝓝 m) := by
    have h0 : Tendsto (fun h : ℝ => m - q * h) (𝓝 (0 : ℝ)) (𝓝 m) := by
      have hq : Tendsto (fun _ : ℝ => q) (𝓝 (0 : ℝ)) (𝓝 q) := tendsto_const_nhds
      have hid : Tendsto (fun h : ℝ => h) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
      have hm : Tendsto (fun _ : ℝ => m) (𝓝 (0 : ℝ)) (𝓝 m) := tendsto_const_nhds
      have h1 := hm.sub (hq.mul hid)
      simpa using h1
    exact Tendsto.mono_left h0 nhdsWithin_le_nhds
  have hlim : Tendsto ((fun _ : ℝ => ve * q + F) / (fun h : ℝ => m - q * h)) (𝓝[≠] 0)
      (𝓝 ((ve * q + F) / m)) := by
    have hnum : Tendsto (fun _ : ℝ => ve * q + F) (𝓝[≠] (0 : ℝ)) (𝓝 (ve * q + F)) :=
      tendsto_const_nhds
    exact hnum.div hden hm'
  exact Tendsto.congr' heq.symm hlim

/-- A differentiable mass history `M` that is burning at `t`, `M' = m' < 0`. A forward parcel step
from `t` to `t + h`, `h > 0`, expels the actual mass `M t - M (t + h)`, at the rate
`q_h = (M t - M (t + h)) / h`, which tends to `-m'`. For small `h > 0` the expelled mass is
nonnegative, the remaining mass `M t - q_h h` is exactly `M (t + h)` and positive, and the step
conserves momentum; its slope at the state `(M t, v)` tends to `(F - ve m') / M t`: the
acceleration `a` of the reduced law `M a = -ve M' + F`. -/
lemma parcel_continuum {M : ℝ → ℝ} {m' t : ℝ} (hM : HasDerivAt M m' t) (hdec : m' < 0)
    (hpos : 0 < M t) (v ve F : ℝ) :
    Tendsto (fun h => (M t - M (t + h)) / h) (𝓝[>] 0) (𝓝 (-m')) ∧
      (∀ᶠ h in 𝓝[>] 0, 0 ≤ M t - M (t + h) ∧ M t - (M t - M (t + h)) / h * h = M (t + h) ∧
        0 < M (t + h) ∧
        M (t + h) * parcelVelocity (M t) v ((M t - M (t + h)) / h) ve F h +
            (M t - M (t + h)) * (v - ve) = M t * v + F * h) ∧
      Tendsto (fun h => (parcelVelocity (M t) v ((M t - M (t + h)) / h) ve F h - v) / h)
        (𝓝[>] 0) (𝓝 ((F - ve * m') / M t)) := by
  have hbase : Tendsto (fun h : ℝ => t + h) (𝓝 (0 : ℝ)) (𝓝 t) := by
    have ht : Tendsto (fun _ : ℝ => t) (𝓝 (0 : ℝ)) (𝓝 t) := tendsto_const_nhds
    have hid : Tendsto (fun h : ℝ => h) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
    have h1 := ht.add hid
    simpa using h1
  have hq : Tendsto (fun h => (M t - M (t + h)) / h) (𝓝[≠] 0) (𝓝 (-m')) := by
    have hslope := hM.tendsto_slope
    have hbase' : Tendsto (fun h : ℝ => t + h) (𝓝[≠] (0 : ℝ)) (𝓝 t) :=
      Tendsto.mono_left hbase nhdsWithin_le_nhds
    have hwith : ∀ᶠ h in 𝓝[≠] (0 : ℝ), t + h ∈ ({t}ᶜ : Set ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hh ⊢
      intro hcon
      exact hh (by linear_combination hcon)
    have hcomp : Tendsto (fun h : ℝ => t + h) (𝓝[≠] (0 : ℝ)) (𝓝[≠] t) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase' hwith
    have h2 := hslope.comp hcomp
    have h2' : Tendsto (fun h : ℝ => slope M t (t + h)) (𝓝[≠] (0 : ℝ)) (𝓝 m') := h2
    have heq : (fun h : ℝ => (M t - M (t + h)) / h)
        =ᶠ[𝓝[≠] 0] (fun h : ℝ => -(slope M t (t + h))) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh0 : h ≠ 0 := by simpa using hh
      have hht : t + h - t ≠ 0 := by
        intro hc
        exact hh0 (by linear_combination hc)
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
      field_simp
      ring
    have h3 : Tendsto (fun h : ℝ => -(slope M t (t + h))) (𝓝[≠] 0) (𝓝 (-m')) := h2'.neg
    exact Tendsto.congr' heq.symm h3
  have hq' : Tendsto (fun h => (M t - M (t + h)) / h) (𝓝[>] 0) (𝓝 (-m')) :=
    hq.mono_left (nhdsWithin_mono _ fun x hx => (Set.mem_Ioi.mp hx).ne')
  have hMt : Tendsto (fun h : ℝ => M (t + h)) (𝓝 (0 : ℝ)) (𝓝 (M t)) :=
    hM.continuousAt.tendsto.comp hbase
  have hposev : ∀ᶠ h in 𝓝 (0 : ℝ), 0 < M (t + h) := hMt.eventually (lt_mem_nhds hpos)
  have hrate : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < (M t - M (t + h)) / h :=
    hq'.eventually (lt_mem_nhds (neg_pos.mpr hdec))
  have hstep : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ M t - M (t + h) ∧
      M t - (M t - M (t + h)) / h * h = M (t + h) ∧ 0 < M (t + h) ∧
      M (t + h) * parcelVelocity (M t) v ((M t - M (t + h)) / h) ve F h +
        (M t - M (t + h)) * (v - ve) = M t * v + F * h := by
    filter_upwards [self_mem_nhdsWithin, hposev.filter_mono nhdsWithin_le_nhds, hrate]
      with h hh hp hr
    have hh0 : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
    have hrem : M t - (M t - M (t + h)) / h * h = M (t + h) := by
      rw [div_mul_cancel₀ _ hh0]
      ring
    have hexp : 0 ≤ M t - M (t + h) := by
      have h1 := (mul_pos hr (Set.mem_Ioi.mp hh)).le
      rwa [div_mul_cancel₀ _ hh0] at h1
    have hmom := (parcel_momentum_iff (m := M t) (q := (M t - M (t + h)) / h) (h := h)
      (by rw [hrem]; exact hp.ne') v ve F
      (parcelVelocity (M t) v ((M t - M (t + h)) / h) ve F h)).mpr rfl
    rw [hrem, div_mul_cancel₀ _ hh0] at hmom
    exact ⟨hexp, hrem, hp, hmom⟩
  have heq : (fun h => (parcelVelocity (M t) v ((M t - M (t + h)) / h) ve F h - v) / h)
      =ᶠ[𝓝[>] 0] ((fun h => ve * ((M t - M (t + h)) / h) + F) / (fun h => M (t + h))) := by
    filter_upwards [self_mem_nhdsWithin, hstep] with h hh hs
    have hh0 : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
    have hmh : M t - (M t - M (t + h)) / h * h ≠ 0 := by
      rw [hs.2.1]
      exact hs.2.2.1.ne'
    simp only [Pi.div_apply]
    rw [parcel_slope_eq hh0 hmh v ve F, hs.2.1]
  have hlim : Tendsto ((fun h => ve * ((M t - M (t + h)) / h) + F) / (fun h => M (t + h)))
      (𝓝[>] 0) (𝓝 ((ve * -m' + F) / M t)) :=
    ((hq'.const_mul ve).add_const F).div (hMt.mono_left nhdsWithin_le_nhds) hpos.ne'
  have hval : (ve * -m' + F) / M t = (F - ve * m') / M t := by
    congr 1
    ring
  rw [hval] at hlim
  exact ⟨hq', hstep, Tendsto.congr' heq.symm hlim⟩

/-- A linear mass history `M (t + h) = M t + m' h` that is burning, `m' < 0`. Every forward step
`h > 0` that leaves positive mass, `0 < M (t + h)` (that is, `h < M t / (-m')`), expels the
nonnegative mass `M t - M (t + h)` at exactly the constant rate `-m'`, and the parcel step with the
constant flow `-m'` leaves exactly the mass `M (t + h)` and conserves momentum: there it is the
actual parcel step. A longer step would leave no mass or negative mass, and is not a parcel step.
The slope of the constant-flow step tends to `(F - ve m') / M t` as `h → 0⁺`. -/
lemma parcel_continuum_linear {M : ℝ → ℝ} {m' t : ℝ} (hlin : ∀ h, M (t + h) = M t + m' * h)
    (hdec : m' < 0) (hpos : 0 < M t) (v ve F : ℝ) :
    (∀ h > 0, 0 < M (t + h) → 0 ≤ M t - M (t + h) ∧ (M t - M (t + h)) / h = -m' ∧
      M t - -m' * h = M (t + h) ∧
      M (t + h) * parcelVelocity (M t) v (-m') ve F h + (M t - M (t + h)) * (v - ve) =
        M t * v + F * h) ∧
      Tendsto (fun h => (parcelVelocity (M t) v (-m') ve F h - v) / h) (𝓝[>] 0)
        (𝓝 ((F - ve * m') / M t)) := by
  refine ⟨fun h hh hMh => ?_, ?_⟩
  · have hrem : M t - -m' * h = M (t + h) := by
      rw [hlin h]
      ring
    have hexp : M t - M (t + h) = -m' * h := by
      rw [hlin h]
      ring
    have hmom := (parcel_momentum_iff (m := M t) (q := -m') (h := h)
      (by rw [hrem]; exact hMh.ne') v ve F (parcelVelocity (M t) v (-m') ve F h)).mpr rfl
    rw [hrem, ← hexp] at hmom
    refine ⟨?_, ?_, hrem, hmom⟩
    · rw [hexp]
      exact (mul_pos (neg_pos.mpr hdec) hh).le
    · rw [hexp, mul_div_assoc, div_self (ne_of_gt hh), mul_one]
  · have hlim := parcel_slope_tendsto hpos v (-m') ve F
    have heq : (ve * (-m') + F) / M t = (F - ve * m') / M t := by
      congr 1
      ring
    rw [heq] at hlim
    exact hlim.mono_left (nhdsWithin_mono _ fun x hx => (Set.mem_Ioi.mp hx).ne')

/-- For `m > 0` and no expelled mass the parcel step is the fixed-mass constant-force velocity. -/
lemma parcelVelocity_zero_flow {m : ℝ} (hm : 0 < m) (v ve F h : ℝ) :
    parcelVelocity m v 0 ve F h = constForceVelocity m v F h := by
  have hm' : m ≠ 0 := ne_of_gt hm
  unfold parcelVelocity constForceVelocity
  simp only [smul_eq_mul, zero_mul, sub_zero]
  field_simp

/-! ## F. Validation -/

/-- For `m > 0`, a positive mass flow at a positive exhaust speed with no external force gives a
positive, hence nonzero, acceleration. -/
lemma parcel_accel_pos {m q ve F : ℝ} (hm : 0 < m) (hq : 0 < q) (hve : 0 < ve) (hF : F = 0) :
    0 < (ve * q + F) / m := by
  subst hF
  positivity

/-- Velocity after one step of the balance that ignores the expelled momentum,
`(m - q h) w_h = m v + F h`, which needs the remaining mass `m - q h` to be nonzero. -/
noncomputable def naiveParcelVelocity (m v q F h : ℝ) : ℝ :=
  (m * v + F * h) / (m - q * h)

/-- Ignoring the expelled momentum, the slope for `m > 0` tends to `(q v + F) / m`. -/
lemma naive_slope_tendsto {m : ℝ} (hm : 0 < m) (v q F : ℝ) :
    Tendsto (fun h => (naiveParcelVelocity m v q F h - v) / h) (𝓝[≠] 0)
      (𝓝 ((q * v + F) / m)) := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have hslope : ∀ h : ℝ, h ≠ 0 → m - q * h ≠ 0 →
      (naiveParcelVelocity m v q F h - v) / h = (q * v + F) / (m - q * h) := by
    intro h hh hmh
    unfold naiveParcelVelocity
    have hmh' : m - h * q ≠ 0 := by
      intro hc
      apply hmh
      linear_combination hc
    field_simp
    ring
  have heq : (fun h : ℝ => (naiveParcelVelocity m v q F h - v) / h)
      =ᶠ[𝓝[≠] 0] ((fun _ : ℝ => q * v + F) / (fun h : ℝ => m - q * h)) := by
    have hpos : ∀ᶠ h in 𝓝[≠] (0 : ℝ), 0 < m - q * h :=
      Eventually.filter_mono nhdsWithin_le_nhds (eventually_parcel_mass_pos hm q)
    filter_upwards [self_mem_nhdsWithin, hpos] with h hh0 hpos
    have hh : h ≠ 0 := by simpa using hh0
    have hmh : m - q * h ≠ 0 := ne_of_gt hpos
    simp only [Pi.div_apply]
    exact hslope h hh hmh
  have hden : Tendsto (fun h : ℝ => m - q * h) (𝓝[≠] (0 : ℝ)) (𝓝 m) := by
    have h0 : Tendsto (fun h : ℝ => m - q * h) (𝓝 (0 : ℝ)) (𝓝 m) := by
      have hq : Tendsto (fun _ : ℝ => q) (𝓝 (0 : ℝ)) (𝓝 q) := tendsto_const_nhds
      have hid : Tendsto (fun h : ℝ => h) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
      have hm : Tendsto (fun _ : ℝ => m) (𝓝 (0 : ℝ)) (𝓝 m) := tendsto_const_nhds
      have h1 := hm.sub (hq.mul hid)
      simpa using h1
    exact Tendsto.mono_left h0 nhdsWithin_le_nhds
  have hlim : Tendsto ((fun _ : ℝ => q * v + F) / (fun h : ℝ => m - q * h)) (𝓝[≠] 0)
      (𝓝 ((q * v + F) / m)) := by
    have hnum : Tendsto (fun _ : ℝ => q * v + F) (𝓝[≠] (0 : ℝ)) (𝓝 (q * v + F)) :=
      tendsto_const_nhds
    exact hnum.div hden hm'
  exact Tendsto.congr' heq.symm hlim

/-- For `m > 0` that limit is the wrong derivative whenever `q (v - ve) ≠ 0`. -/
lemma naive_limit_ne {m q v ve : ℝ} (hm : 0 < m) (hq : q ≠ 0) (hv : v ≠ ve) (F : ℝ) :
    (q * v + F) / m ≠ (ve * q + F) / m := by
  intro h
  have hm' : m ≠ 0 := ne_of_gt hm
  have h2 : q * v + F = ve * q + F := by
    have hcon := congrArg (fun x : ℝ => x * m) h
    rwa [div_mul_cancel₀ _ hm', div_mul_cancel₀ _ hm'] at hcon
  have h3 : q * (v - ve) = 0 := by linear_combination h2
  have h4 : v - ve = 0 := by
    rcases mul_eq_zero.mp h3 with hq0 | hv0
    · exact absurd hq0 hq
    · exact hv0
  exact hv (sub_eq_zero.mp h4)

section SeparateFlowThrust

open MeasureTheory ControlVolumes
open MathlibExt.Probability.FokkerPlanck (divergence)

/-! ## G. Separate-flow thrust from the port balance -/

/-- The separate-flow thrust `T = ṁ_out v_e - ṁ_in v_in + (p_e - p_a) A_e - (p_in - p_a) A_in`,
positive forward, of an engine at rest with an inlet port (mass flow `ṁ_in`, axial velocity
`v_in`, pressure `p_in`, area `A_in`) and an exhaust port (`ṁ_out`, `v_e`, `p_e`, `A_e`) in an
ambient at pressure `p_a`; the velocities are relative to the engine, positive aft. -/
def separateFlowThrust (mdotIn vIn pIn AIn mdotOut vE pE AE pA : ℝ) : ℝ :=
  mdotOut * vE - mdotIn * vIn + (pE - pA) * AE - (pIn - pA) * AIn

/-- **Stand force from the port balance.** Take the axial momentum balance of the control volume
in the port form of `ControlVolumes.hasDerivAt_momentum_twoPort`: the momentum rate `P'` is the
inflow `ṁ_in v_in + ṁ_f v_f` minus the outflow `ṁ_out v_e`, minus the port pressure forces with
outward normals `-1` (inlet) and `+1` (exhaust), plus the ambient force `F_lat` on the rest of the
surface and the axial force `F` of the stand on the contents. A uniform ambient pressure has zero
resultant over the closed surface (`hamb`). Then `F = T + P' - ṁ_f v_f`. -/
lemma standForce_eq_separateFlowThrust_add {mdotIn vIn pIn AIn mdotF vF mdotOut vE pE AE pA Flat
    F dP : ℝ} (hamb : Flat - pA * AIn * (-1) - pA * AE * 1 = 0)
    (hbal : dP = mdotIn * vIn + mdotF * vF - mdotOut * vE - (pIn * AIn * (-1) + pE * AE * 1) +
      Flat + F) :
    F = separateFlowThrust mdotIn vIn pIn AIn mdotOut vE pE AE pA + dP - mdotF * vF := by
  unfold separateFlowThrust
  linear_combination -hbal - hamb

/-- **Steady separate-flow thrust.** In a steady state (`P' = 0`) with negligible fuel feed
momentum (`v_f = 0`), the axial force of the stand on the control volume, which the engine exerts
forward on the stand, is `T = ṁ_out v_e - ṁ_in v_in + (p_e - p_a) A_e - (p_in - p_a) A_in`. -/
lemma standForce_eq_separateFlowThrust {mdotIn vIn pIn AIn mdotF vF mdotOut vE pE AE pA Flat
    F : ℝ} (hamb : Flat - pA * AIn * (-1) - pA * AE * 1 = 0) (hfeed : vF = 0)
    (hbal : 0 = mdotIn * vIn + mdotF * vF - mdotOut * vE - (pIn * AIn * (-1) + pE * AE * 1) +
      Flat + F) :
    F = separateFlowThrust mdotIn vIn pIn AIn mdotOut vE pE AE pA := by
  rw [standForce_eq_separateFlowThrust_add hamb hbal, hfeed]
  ring

/-- **The box balance of `ControlVolumes`.** For a fluid in a fixed box with the inlet on the face
`x₀ = a₀` and the exhaust on the face `x₀ = b₀`, both of area `A₀ = faceArea a b 0`, under the
hypotheses of `ControlVolumes.hasDerivAt_momentum_twoPort` (pressure-only uniform port data,
impermeable side walls), with a stationary momentum and no axial body force, the axial component of
the traction resultant of the side walls on the fluid is the separate-flow thrust with equal port
areas and port mass flows `ṁ = ρ A₀ v₀`, for every ambient pressure `p_a`. -/
lemma wallForce_eq_separateFlowThrust {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {ρ : ℝ → (Fin (n + 1) → ℝ) → ℝ} {v f : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    {σ : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ} {t : ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hv : ContDiff ℝ 1 (Function.uncurry v))
    (hσ : ContDiffOn ℝ 1 (σ t) U) (hf : ∀ j, IntegrableOn (fun x => f t x j) (Icc a b))
    (hlaw : ∀ j, ∀ x ∈ Icc a b,
      deriv (fun τ => ρ τ x * v τ x j) t + divergence (momentumFlux (ρ t) (v t) (σ t) j) x =
        f t x j)
    {ρi ρo pi po : ℝ} {vi vo : Fin (n + 1) → ℝ}
    (hρi : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      ρ t ((0 : Fin (n + 1)).insertNth (a 0) y) = ρi)
    (hvi : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      v t ((0 : Fin (n + 1)).insertNth (a 0) y) = vi)
    (hσi : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      (fun j => σ t ((0 : Fin (n + 1)).insertNth (a 0) y) j 0) = -(pi • Pi.single 0 1))
    (hρo : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      ρ t ((0 : Fin (n + 1)).insertNth (b 0) y) = ρo)
    (hvo : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      v t ((0 : Fin (n + 1)).insertNth (b 0) y) = vo)
    (hσo : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      (fun j => σ t ((0 : Fin (n + 1)).insertNth (b 0) y) j 0) = -(po • Pi.single 0 1))
    (hwall : ∀ i, i ≠ 0 → ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      v t (i.insertNth (b i) y) i = 0 ∧ v t (i.insertNth (a i) y) i = 0)
    (hsteady : HasDerivAt (fun τ => fun j => ∫ x in Icc a b, ρ τ x * v τ x j) 0 t)
    (hbody : ∫ x in Icc a b, f t x 0 = 0) (pa : ℝ) :
    (∑ i : Fin n, faceTractionResultant a b (σ t) i.succ) 0 =
      separateFlowThrust (ρi * faceArea a b 0 * vi 0) (vi 0) pi (faceArea a b 0)
        (ρo * faceArea a b 0 * vo 0) (vo 0) po (faceArea a b 0) pa := by
  have h := hasDerivAt_momentum_twoPort hab hU hbox hρ hv hσ hf hlaw hρi hvi hσi hρo hvo hσo hwall
  have h0 := congrFun (h.unique hsteady) 0
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
    Pi.single_eq_same, Pi.zero_apply, Finset.sum_apply, hbody] at h0
  unfold separateFlowThrust
  simp only [Finset.sum_apply]
  linarith

/-! ## H. Rocket and air-breather -/

/-- **Rocket.** With no inlet stream and no air-capture area (`ṁ_in = 0`, `A_in = 0`) the steady
mass balance `ṁ_out = ṁ_in + ṁ_f` makes the exhaust carry the propellant flow, and
`T = ṁ_f v_e + (p_e - p_a) A_e`, whatever `v_in` and `p_in`. -/
lemma separateFlowThrust_rocket {mdotIn AIn mdotF mdotOut : ℝ} (hin : mdotIn = 0) (hA : AIn = 0)
    (hmass : mdotOut = mdotIn + mdotF) (vIn pIn vE pE AE pA : ℝ) :
    separateFlowThrust mdotIn vIn pIn AIn mdotOut vE pE AE pA = mdotF * vE + (pE - pA) * AE := by
  rw [hmass, hin, hA, separateFlowThrust]
  ring

/-- **A rocket burn gives nonzero thrust.** A rocket (`ṁ_in = 0`, `A_in = 0`) with propellant
flow `ṁ_f > 0`, exhaust velocity `v_e > 0` and `p_e ≥ p_a`, `A_e ≥ 0` has positive thrust. -/
lemma separateFlowThrust_rocket_pos {mdotIn AIn mdotF mdotOut vE pE AE pA : ℝ} (hin : mdotIn = 0)
    (hA : AIn = 0) (hmass : mdotOut = mdotIn + mdotF) (hf : 0 < mdotF) (hvE : 0 < vE)
    (hp : pA ≤ pE) (hAE : 0 ≤ AE) (vIn pIn : ℝ) :
    0 < separateFlowThrust mdotIn vIn pIn AIn mdotOut vE pE AE pA := by
  rw [separateFlowThrust_rocket hin hA hmass]
  have h1 : 0 < mdotF * vE := mul_pos hf hvE
  have h2 : 0 ≤ (pE - pA) * AE := mul_nonneg (by linarith) hAE
  linarith

/-- **Air-breather.** With `p_in = p_a` at the capture plane and the steady mass balance
`ṁ_out = ṁ_in + ṁ_f`, `T = (ṁ_in + ṁ_f) v_e - ṁ_in v_in + (p_e - p_a) A_e`. -/
lemma separateFlowThrust_airBreather {mdotIn pIn mdotF mdotOut pA : ℝ} (hcap : pIn = pA)
    (hmass : mdotOut = mdotIn + mdotF) (vIn AIn vE pE AE : ℝ) :
    separateFlowThrust mdotIn vIn pIn AIn mdotOut vE pE AE pA =
      (mdotIn + mdotF) * vE - mdotIn * vIn + (pE - pA) * AE := by
  rw [hmass, hcap, separateFlowThrust]
  ring

/-- **Exhaust flow of an air-breather.** Under the steady mass balance `ṁ_out = ṁ_in + ṁ_f`,
fuel `ṁ_f > 0` makes the exhaust flow exceed the inlet flow; the exhaust and inlet flows are equal
exactly when `ṁ_f = 0`, and the equal-flow thrust (exhaust flow replaced by `ṁ_in`) falls short
of the thrust by `ṁ_f v_e`. -/
lemma airBreather_exhaustFlow {mdotIn mdotF mdotOut : ℝ} (hmass : mdotOut = mdotIn + mdotF)
    (vIn pIn AIn vE pE AE pA : ℝ) :
    (0 < mdotF → mdotIn < mdotOut) ∧ (mdotOut = mdotIn ↔ mdotF = 0) ∧
      separateFlowThrust mdotIn vIn pIn AIn mdotOut vE pE AE pA -
          separateFlowThrust mdotIn vIn pIn AIn mdotIn vE pE AE pA = mdotF * vE := by
  subst hmass
  refine ⟨fun h => by linarith, ⟨fun h => by linarith, fun h => by rw [h, add_zero]⟩, ?_⟩
  unfold separateFlowThrust
  ring

/-! ## I. Effective exhaust velocity and specific impulse -/

/-- The effective exhaust velocity `c = T / ṁ_out` of a thrust `T` at the exhaust mass flow
`ṁ_out`. -/
noncomputable def effectiveExhaustVelocity (T mdotOut : ℝ) : ℝ := T / mdotOut

/-- **Total-flow specific impulse.** `T / (ṁ_out g0) = c / g0`. -/
lemma specificImpulse_totalFlow_eq (T mdotOut g0 : ℝ) :
    specificImpulse T mdotOut g0 = effectiveExhaustVelocity T mdotOut / g0 := by
  unfold specificImpulse effectiveExhaustVelocity
  rw [div_div]

/-- **Fuel-flow specific impulse.** For positive exhaust and fuel flows, the fuel-flow specific
impulse `T / (ṁ_f g0)` is the total-flow one times `ṁ_out / ṁ_f`. -/
lemma specificImpulse_fuelFlow_eq {mdotOut mdotF : ℝ} (hout : 0 < mdotOut) (hf : 0 < mdotF)
    (T g0 : ℝ) :
    specificImpulse T mdotF g0 = specificImpulse T mdotOut g0 * (mdotOut / mdotF) := by
  unfold specificImpulse
  rcases eq_or_ne g0 0 with rfl | hg
  · simp
  · field_simp

/-- **Rocket: the two specific impulses coincide.** With no inlet stream the exhaust flow is the
propellant flow, so the total-flow and fuel-flow specific impulses are equal. -/
lemma specificImpulse_rocket_flows_eq {mdotIn mdotF mdotOut : ℝ} (hin : mdotIn = 0)
    (hmass : mdotOut = mdotIn + mdotF) (T g0 : ℝ) :
    specificImpulse T mdotOut g0 = specificImpulse T mdotF g0 := by
  rw [hmass, hin, zero_add]

/-- **Air-breather: the two specific impulses differ.** With inlet flow `ṁ_in > 0`, fuel flow
`ṁ_f > 0`, thrust `T > 0` and `g0 > 0`, the total-flow specific impulse is strictly smaller than
the fuel-flow one. -/
lemma specificImpulse_totalFlow_lt_fuelFlow {mdotIn mdotF mdotOut T g0 : ℝ} (hin : 0 < mdotIn)
    (hf : 0 < mdotF) (hmass : mdotOut = mdotIn + mdotF) (hT : 0 < T) (hg0 : 0 < g0) :
    specificImpulse T mdotOut g0 < specificImpulse T mdotF g0 := by
  unfold specificImpulse
  rw [hmass]
  apply div_lt_div_of_pos_left hT (by positivity)
  nlinarith

/-- **Pressure-matched rocket.** A rocket with `p_e = p_a` and positive propellant flow has the
effective exhaust velocity `c = v_e`, so its specific impulse is `v_e / g0`, as in
`specificImpulse_eq_of_law`. -/
lemma effectiveExhaustVelocity_rocket_matched {mdotIn AIn mdotF mdotOut pE pA : ℝ}
    (hin : mdotIn = 0) (hA : AIn = 0) (hmass : mdotOut = mdotIn + mdotF) (hf : 0 < mdotF)
    (hp : pE = pA) (vIn pIn vE AE g0 : ℝ) :
    effectiveExhaustVelocity (separateFlowThrust mdotIn vIn pIn AIn mdotOut vE pE AE pA)
        mdotOut = vE ∧
      specificImpulse (separateFlowThrust mdotIn vIn pIn AIn mdotOut vE pE AE pA) mdotOut g0 =
        vE / g0 := by
  have hc : effectiveExhaustVelocity (separateFlowThrust mdotIn vIn pIn AIn mdotOut vE pE AE pA)
      mdotOut = vE := by
    rw [effectiveExhaustVelocity, separateFlowThrust_rocket hin hA hmass, hp, hmass, hin,
      zero_add, sub_self, zero_mul, add_zero]
    field_simp
  exact ⟨hc, by rw [specificImpulse_totalFlow_eq, hc]⟩

end SeparateFlowThrust

/-! ## J. Staged burns and dry-mass jettison -/

/-- A jettison with zero relative velocity leaves the velocity unchanged: a vehicle of mass `m₁` at
velocity `v` drops the mass `m₁ - m₂`, which keeps the velocity `v`, and the remaining mass `m₂`
moves at `w`. If `m₂ ≠ 0` (a positive remaining mass in the model), momentum is conserved,
`m₂ w + (m₁ - m₂) v = m₁ v`, exactly when `w = v`. The identity needs only `m₂ ≠ 0`; a jettison
is the case `m₂ ≤ m₁`, which `staged_velocity_increment` requires of every transition. -/
lemma jettison_velocity_eq {m₁ m₂ v w : ℝ} (hm₂ : m₂ ≠ 0) :
    m₂ * w + (m₁ - m₂) * v = m₁ * v ↔ w = v := by
  constructor
  · intro h
    have h2 : m₂ * w = m₂ * v := by linear_combination h
    exact mul_left_cancel₀ hm₂ h2
  · intro h
    rw [h]
    ring

/-- Staged burn and jettison accounting. Burns `i ≤ n` on `[0, tb i]` with positive mass, exhaust
speed `ve i` and the reduced law; between burn `i` and burn `i + 1` a jettison with zero relative
velocity from mass `m i (tb i)` to mass `m (i + 1) 0 ≤ m i (tb i)` that conserves momentum. The
velocity gained from the start of burn `0` to the end of burn `n` is the sum of the burn increments
`ve i * log (m i 0 / m i (tb i))`; the jettisoned masses enter no logarithm. Neither the mass drop
nor the sign of the exhaust speeds is needed for the identity: the drop restricts the statement to
jettisons, and the model's positive stage-specific `ve i` are a special case. -/
lemma staged_velocity_increment (n : ℕ) {m v m' v' : ℕ → ℝ → ℝ} {ve tb : ℕ → ℝ}
    (htb : ∀ i ≤ n, 0 ≤ tb i) (hm : ∀ i ≤ n, ∀ t ∈ Icc 0 (tb i), HasDerivAt (m i) (m' i t) t)
    (hv : ∀ i ≤ n, ∀ t ∈ Icc 0 (tb i), HasDerivAt (v i) (v' i t) t)
    (hpos : ∀ i ≤ n, ∀ t ∈ Icc 0 (tb i), 0 < m i t)
    (hlaw : ∀ i ≤ n, ∀ t ∈ Icc 0 (tb i), m i t * v' i t = -ve i * m' i t)
    (_hdrop : ∀ i < n, m (i + 1) 0 ≤ m i (tb i))
    (hjet : ∀ i < n, m (i + 1) 0 * v (i + 1) 0 + (m i (tb i) - m (i + 1) 0) * v i (tb i) =
      m i (tb i) * v i (tb i)) :
    v n (tb n) - v 0 0 = ∑ i ∈ Finset.range (n + 1), ve i * Real.log (m i 0 / m i (tb i)) := by
  clear _hdrop
  revert htb hm hv hpos hlaw hjet
  induction n with
  | zero =>
    intro htb hm hv hpos hlaw hjet
    change v 0 (tb 0) - v 0 0 = ∑ i ∈ Finset.range 1, ve i * Real.log (m i 0 / m i (tb i))
    rw [Finset.sum_range_one]
    exact velocity_increment_eq_log (htb 0 le_rfl) (hm 0 le_rfl) (hv 0 le_rfl)
      (hpos 0 le_rfl) (hlaw 0 le_rfl)
  | succ n ih =>
    intro htb hm hv hpos hlaw hjet
    have htb' : ∀ i ≤ n, 0 ≤ tb i := fun i hi => htb i (le_trans hi (Nat.le_succ n))
    have hm' : ∀ i ≤ n, ∀ t ∈ Icc 0 (tb i), HasDerivAt (m i) (m' i t) t :=
      fun i hi => hm i (le_trans hi (Nat.le_succ n))
    have hv' : ∀ i ≤ n, ∀ t ∈ Icc 0 (tb i), HasDerivAt (v i) (v' i t) t :=
      fun i hi => hv i (le_trans hi (Nat.le_succ n))
    have hpos' : ∀ i ≤ n, ∀ t ∈ Icc 0 (tb i), 0 < m i t :=
      fun i hi => hpos i (le_trans hi (Nat.le_succ n))
    have hlaw' : ∀ i ≤ n, ∀ t ∈ Icc 0 (tb i), m i t * v' i t = -ve i * m' i t :=
      fun i hi => hlaw i (le_trans hi (Nat.le_succ n))
    have hjet' : ∀ i < n, m (i + 1) 0 * v (i + 1) 0 + (m i (tb i) - m (i + 1) 0) *
        v i (tb i) = m i (tb i) * v i (tb i) :=
      fun i hi => hjet i (lt_of_lt_of_le hi (Nat.le_succ n))
    have ih' := ih htb' hm' hv' hpos' hlaw' hjet'
    have hburn := velocity_increment_eq_log (htb (n + 1) le_rfl) (hm (n + 1) le_rfl)
      (hv (n + 1) le_rfl) (hpos (n + 1) le_rfl) (hlaw (n + 1) le_rfl)
    have hjmass : m (n + 1) 0 ≠ 0 :=
      ne_of_gt (hpos (n + 1) le_rfl 0 ⟨le_refl 0, htb (n + 1) le_rfl⟩)
    have hveq : v (n + 1) 0 = v n (tb n) :=
      (jettison_velocity_eq hjmass).mp (hjet n (Nat.lt_succ_self n))
    rw [Finset.sum_range_succ]
    linear_combination hburn + hveq + ih'

/-- Counting dry mass as propellant overstates the increment: for `ve > 0`, `m₀ > 0` and a
nonzero drop from `m₁` to `m₂ > 0`, a burn logarithm that also covers the drop exceeds the true
burn increment by `ve * log (m₁ / m₂) > 0`. -/
lemma jettison_as_propellant_overstates {ve m₀ m₁ m₂ : ℝ} (hve : 0 < ve) (hm₀ : 0 < m₀)
    (hm₂ : 0 < m₂) (hdrop : m₂ < m₁) :
    ve * Real.log (m₀ / m₂) = ve * Real.log (m₀ / m₁) + ve * Real.log (m₁ / m₂) ∧
      ve * Real.log (m₀ / m₁) < ve * Real.log (m₀ / m₂) := by
  have hm₁ : 0 < m₁ := lt_trans hm₂ hdrop
  have hne₀₁ : m₀ / m₁ ≠ 0 := div_ne_zero (ne_of_gt hm₀) (ne_of_gt hm₁)
  have hne₁₂ : m₁ / m₂ ≠ 0 := div_ne_zero (ne_of_gt hm₁) (ne_of_gt hm₂)
  have hm₁' : m₁ ≠ 0 := ne_of_gt hm₁
  have hm₂' : m₂ ≠ 0 := ne_of_gt hm₂
  have hsplit : m₀ / m₂ = (m₀ / m₁) * (m₁ / m₂) := by
    field_simp
  have hlog : Real.log (m₀ / m₂) = Real.log (m₀ / m₁) + Real.log (m₁ / m₂) := by
    rw [hsplit, Real.log_mul hne₀₁ hne₁₂]
  have heq : ve * Real.log (m₀ / m₂)
      = ve * Real.log (m₀ / m₁) + ve * Real.log (m₁ / m₂) := by
    rw [hlog]
    ring
  have hpos : 0 < ve * Real.log (m₁ / m₂) := by
    apply mul_pos hve
    apply Real.log_pos
    rw [one_lt_div hm₂]
    exact hdrop
  refine ⟨heq, ?_⟩
  rw [heq]
  linarith

end PhyslibExt.Mechanics.PropulsionPorts
