/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PhyslibExt.Mechanics.PropulsionPorts

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Space trajectory models: a thrust-only rendezvous with independent terminal data

A gravity-free, collinear pilot of a thrust-only rendezvous in normalized units. The vehicle
starts from rest at the origin with mass `2`, expels propellant at the constant mass flow `1`
with exhaust speed `1` on the burn interval `[0, 1]`, so `m t = 2 - t` and the thrust is `1`.
The reduced variable-mass law `m v' = -ve * m'` of `PhyslibExt.Mechanics.PropulsionPorts` is
solved by `v t = log (2 / (2 - t))`, whose integral from the origin is
`x t = t + (2 - t) * log ((2 - t) / 2)`. A target coasting at the constant speed `log 2` along
`x_target t = 1 - 2 * log 2 + t * log 2` is met at `t = 1` with equal position `1 - log 2` and
equal velocity `log 2`, while the mass stays positive.

## i. Overview

* The burn. `burnMass`, `burnVelocity` and `burnPosition` are the prescribed histories. On
  `[0, 1]` the mass is positive, the law holds with exhaust speed `1`, and its common value, the
  thrust, is `1`. The velocity gained, `log 2`, is the ideal rocket equation
  `velocity_increment_eq_log` at `ve = 1`, `m 0 / m 1 = 2`; the position is the integral of the
  velocity by the fundamental theorem of calculus.
* The target. `targetPosition` has its own terminal data, fixed explicitly and independently of
  the burn: speed `log 2` at all times and position `1 - log 2` at `t = 1`.
* Rendezvous. At `t = 1` both positions are `1 - log 2` and both have derivative `log 2`.
* Boundaries, checked in the test module. The mass vanishes at `t = 2`, outside the burn
  interval; there Lean's totalized `2 / 0 = 0` and `log 0 = 0` turn the velocity formula into
  the junk value `0`.

Signs: positions and velocities are measured along the thrust direction; the exhaust leaves
backward, `m' = -1 < 0`, and the vehicle speeds up, `v' = 1 / (2 - t) > 0`.

Model inputs: no gravity, drag or other external force; one line of motion; the mass history,
exhaust speed and target are fixed explicitly. This is not a general orbital rendezvous, not a
guidance law and not an optimality result; no empirical adequacy or vehicle safety claim.

## ii. Key results

- `burnMass`, `burnVelocity`, `burnPosition`, `targetPosition`: the prescribed histories.
- `hasDerivAt_burnMass`, `burnMass_pos`, `hasDerivAt_burnVelocity`, `burn_law`: mass flow `1`,
  positive mass, the law with exhaust speed `1` and thrust `1`.
- `burn_initial`, `hasDerivAt_burnPosition`, `burnVelocity_increment`,
  `burnPosition_sub_eq_integral`: rest at the origin, `x' = v`, the ideal rocket equation and the
  displacement as the integral of the velocity.
- `hasDerivAt_targetPosition`, `rendezvous`: the target's constant speed and the matched
  terminal position and velocity at `t = 1`.
- The nonzero burn and the excluded depletion time are checked in
  `PhyslibExtTest.Mechanics.SpaceTrajectoryModelsTest`.

## iii. Table of contents

- D. The prescribed burn
- E. Velocity and position histories
- F. The target and the rendezvous

## iv. References

- G. P. Sutton and O. Biblarz, *Rocket Propulsion Elements*, 9th edition, chapters 2 and 4
  (thrust, effective exhaust velocity, ideal rocket equation).
- H. D. Curtis, *Orbital Mechanics for Engineering Students*, rocket vehicle dynamics chapter.
- `PhyslibExt.Mechanics.PropulsionPorts` (`velocity_increment_eq_log`).
-/

@[expose] public section

namespace PhyslibExt.Mechanics.SpaceTrajectoryModels

open Set PhyslibExt.Mechanics.PropulsionPorts

/-! ## D. The prescribed burn -/

/-- The mass history `m t = 2 - t` of the normalized burn: initial mass `2` and propellant mass
flow `1`, so the mass falls from `2` to `1` on the burn interval `[0, 1]`. -/
def burnMass (t : ℝ) : ℝ := 2 - t

/-- The velocity history `v t = log (2 / (2 - t))` of the burn, from rest at `t = 0`. -/
noncomputable def burnVelocity (t : ℝ) : ℝ := Real.log (2 / (2 - t))

/-- The position history `x t = t + (2 - t) * log ((2 - t) / 2)` of the burn, from the origin at
`t = 0`. -/
noncomputable def burnPosition (t : ℝ) : ℝ := t + (2 - t) * Real.log ((2 - t) / 2)

/-- The target `x_target t = 1 - 2 * log 2 + t * log 2`, coasting at the constant speed `log 2`.
Its terminal data are fixed explicitly, independently of the burn. -/
noncomputable def targetPosition (t : ℝ) : ℝ := 1 - 2 * Real.log 2 + t * Real.log 2

/-- The mass flow is constant: `m' = -1` at every time. -/
lemma hasDerivAt_burnMass (t : ℝ) : HasDerivAt burnMass (-1) t := by
  have h1 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 t := hasDerivAt_const t 2
  have h2 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h : HasDerivAt (fun i : ℝ => (2 : ℝ) - i) (0 - 1) t := h1.fun_sub h2
  have hderiv : (0 : ℝ) - 1 = -1 := by norm_num
  rw [hderiv] at h
  exact h

/-- The mass stays positive on the burn interval `[0, 1]`. -/
lemma burnMass_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < burnMass t := by
  rw [mem_Icc] at ht
  obtain ⟨-, h1⟩ := ht
  unfold burnMass
  linarith

/-- Before depletion (`t < 2`) the velocity has derivative `v' = 1 / (2 - t)`. -/
lemma hasDerivAt_burnVelocity {t : ℝ} (ht : t < 2) :
    HasDerivAt burnVelocity (1 / (2 - t)) t := by
  have hpos : (0 : ℝ) < 2 - t := by linarith
  have h2t : (2 : ℝ) - t ≠ 0 := ne_of_gt hpos
  have hne : (2 : ℝ) / (2 - t) ≠ 0 := div_ne_zero (by norm_num) h2t
  have hden : HasDerivAt (fun x : ℝ => (2 : ℝ) - x) (-1) t := hasDerivAt_burnMass t
  have hnum : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 t := hasDerivAt_const t 2
  have hdiv : HasDerivAt (fun x : ℝ => (2 : ℝ) / (2 - x))
      ((0 * (2 - t) - 2 * (-1)) / (2 - t) ^ 2) t :=
    hnum.fun_div hden h2t
  have hlog : HasDerivAt (fun y : ℝ => Real.log (2 / (2 - y)))
      ((0 * (2 - t) - 2 * (-1)) / (2 - t) ^ 2 / (2 / (2 - t))) t :=
    hdiv.log hne
  have hderiv : (0 * (2 - t) - 2 * (-1)) / (2 - t) ^ 2 / (2 / (2 - t)) = 1 / (2 - t) := by
    field_simp
    ring
  rw [hderiv] at hlog
  exact hlog

/-- On `[0, 1]` the burn obeys the reduced variable-mass law `m v' = -ve * m'` with exhaust speed
`ve = 1` and `m' = -1`, and the common value, the thrust `ve * (-m')`, is `1`. -/
lemma burn_law {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    burnMass t * (1 / (2 - t)) = -1 * (-1) ∧ burnMass t * (1 / (2 - t)) = 1 := by
  have hne : (2 : ℝ) - t ≠ 0 := by
    have h := burnMass_pos ht
    unfold burnMass at h
    exact ne_of_gt h
  have h : (2 - t) * (1 / (2 - t)) = 1 := by field_simp
  have h' : burnMass t * (1 / (2 - t)) = 1 := h
  exact ⟨by rw [h']; norm_num, h'⟩

/-! ## E. Velocity and position histories -/

/-- The burn starts from rest at the origin: `x 0 = 0` and `v 0 = 0`. -/
lemma burn_initial : burnPosition 0 = 0 ∧ burnVelocity 0 = 0 := by
  have h1 : ((2 : ℝ) - 0) / 2 = 1 := by norm_num
  have h2 : (2 : ℝ) / ((2 : ℝ) - 0) = 1 := by norm_num
  constructor
  · unfold burnPosition
    rw [h1, Real.log_one, mul_zero, add_zero]
  · unfold burnVelocity
    rw [h2, Real.log_one]

/-- Before depletion (`t < 2`) the position has derivative `x' = v`. -/
lemma hasDerivAt_burnPosition {t : ℝ} (ht : t < 2) :
    HasDerivAt burnPosition (burnVelocity t) t := by
  have hpos : (0 : ℝ) < 2 - t := by linarith
  have h2t : (2 : ℝ) - t ≠ 0 := ne_of_gt hpos
  have hg_ne : ((2 : ℝ) - t) / 2 ≠ 0 := div_ne_zero h2t (by norm_num)
  have hden : HasDerivAt (fun x : ℝ => (2 : ℝ) - x) (-1) t := hasDerivAt_burnMass t
  have hg : HasDerivAt (fun x : ℝ => ((2 : ℝ) - x) / 2) (-1 / 2) t :=
    hden.div_const 2
  have hlogg : HasDerivAt (fun x : ℝ => Real.log (((2 : ℝ) - x) / 2))
      ((-1 / 2) / (((2 : ℝ) - t) / 2)) t :=
    hg.log hg_ne
  have hmul : HasDerivAt (fun x : ℝ => ((2 : ℝ) - x) * Real.log (((2 : ℝ) - x) / 2))
      (-1 * Real.log (((2 : ℝ) - t) / 2) + (2 - t) * ((-1 / 2) / (((2 : ℝ) - t) / 2))) t :=
    hden.fun_mul hlogg
  have hid : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have hadd : HasDerivAt (fun x : ℝ => x + ((2 : ℝ) - x) * Real.log (((2 : ℝ) - x) / 2))
      (1 + (-1 * Real.log (((2 : ℝ) - t) / 2) + (2 - t) * ((-1 / 2) / (((2 : ℝ) - t) / 2)))) t :=
    hid.fun_add hmul
  have hmul_eq : (2 - t) * ((-1 / 2) / (((2 : ℝ) - t) / 2)) = -1 := by
    field_simp
  have hlog_eq : Real.log (2 / (2 - t)) = -Real.log (((2 : ℝ) - t) / 2) := by
    have hinv : (2 : ℝ) / (2 - t) = (((2 : ℝ) - t) / 2)⁻¹ := (inv_div _ _).symm
    rw [hinv, Real.log_inv]
  have hderiv : 1 + (-1 * Real.log (((2 : ℝ) - t) / 2) + (2 - t) * ((-1 / 2) / (((2 : ℝ) - t) / 2)))
      = Real.log (2 / (2 - t)) := by
    rw [hmul_eq, hlog_eq]
    ring
  rw [hderiv] at hadd
  exact hadd

/-- The ideal rocket equation `velocity_increment_eq_log` for this burn: the velocity gained on
`[0, 1]` is `ve * log (m 0 / m 1)` with `ve = 1`. -/
lemma burnVelocity_increment :
    burnVelocity 1 - burnVelocity 0 = 1 * Real.log (burnMass 0 / burnMass 1) := by
  have htb : (0 : ℝ) ≤ 1 := by norm_num
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt burnMass (-1) t :=
    fun t _ => hasDerivAt_burnMass t
  have hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt burnVelocity (1 / (2 - t)) t := by
    intro t ht
    rw [mem_Icc] at ht
    exact hasDerivAt_burnVelocity (by linarith)
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < burnMass t := fun t ht => burnMass_pos ht
  have hlaw : ∀ t ∈ Icc (0 : ℝ) 1, burnMass t * (1 / (2 - t)) = -1 * (-1) := by
    intro t ht
    exact (burn_law ht).1
  exact velocity_increment_eq_log (m := burnMass) (v := burnVelocity)
    (m' := fun _ => (-1 : ℝ)) (v' := fun t => 1 / (2 - t)) (ve := (1 : ℝ)) (tb := (1 : ℝ))
    htb hm hv hpos hlaw

/-- The displacement over the burn is the integral of the velocity: `x 1 - x 0 = ∫₀¹ v`. -/
lemma burnPosition_sub_eq_integral :
    burnPosition 1 - burnPosition 0 = ∫ t in (0 : ℝ)..1, burnVelocity t := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt burnPosition (burnVelocity x) x := by
    rw [uIcc_of_le h01]
    intro x hx
    rw [mem_Icc] at hx
    exact hasDerivAt_burnPosition (by linarith)
  have hcont : ContinuousOn burnVelocity (Icc (0 : ℝ) 1) := by
    intro x hx
    rw [mem_Icc] at hx
    exact (hasDerivAt_burnVelocity (by linarith : x < 2)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable burnVelocity MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc h01 hcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  exact hFTC.symm

/-! ## F. The target and the rendezvous -/

/-- The target coasts at the constant speed `log 2`. -/
lemma hasDerivAt_targetPosition (t : ℝ) : HasDerivAt targetPosition (Real.log 2) t := by
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ) - 2 * Real.log 2) 0 t :=
    hasDerivAt_const t _
  have hid : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have hmul : HasDerivAt (fun x : ℝ => x * Real.log 2) (1 * Real.log 2) t :=
    hid.mul_const (Real.log 2)
  have hadd : HasDerivAt (fun i : ℝ => (1 - 2 * Real.log 2) + i * Real.log 2)
      (0 + 1 * Real.log 2) t :=
    hconst.fun_add hmul
  have hderiv : (0 : ℝ) + 1 * Real.log 2 = Real.log 2 := by ring
  rw [hderiv] at hadd
  exact hadd

/-- Rendezvous at `t = 1`: the positions agree, the burn's velocity is the target's speed
`log 2`, both positions have derivative `log 2` at `t = 1`, and the mass stays positive on the
burn interval. -/
lemma rendezvous :
    burnPosition 1 = targetPosition 1 ∧ burnVelocity 1 = Real.log 2 ∧
      HasDerivAt burnPosition (Real.log 2) 1 ∧ HasDerivAt targetPosition (Real.log 2) 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, 0 < burnMass t := by
  have h21 : ((2 : ℝ) - 1) / 2 = 1 / 2 := by norm_num
  have h2t1 : (2 : ℝ) / ((2 : ℝ) - 1) = 2 := by norm_num
  have hlog_half : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    have h : ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ := by norm_num
    rw [h, Real.log_inv]
  have hv1 : burnVelocity 1 = Real.log 2 := by
    unfold burnVelocity
    rw [h2t1]
  have hx1 : burnPosition 1 = 1 - Real.log 2 := by
    unfold burnPosition
    rw [h21, hlog_half]
    ring
  have ht1 : targetPosition 1 = 1 - Real.log 2 := by
    unfold targetPosition
    ring
  have hpos1 : burnPosition 1 = targetPosition 1 := by rw [hx1, ht1]
  have hderiv : HasDerivAt burnPosition (Real.log 2) 1 := by
    have h := hasDerivAt_burnPosition (show (1 : ℝ) < 2 by norm_num)
    rw [hv1] at h
    exact h
  exact ⟨hpos1, hv1, hderiv, hasDerivAt_targetPosition 1, fun t ht => burnMass_pos ht⟩

end PhyslibExt.Mechanics.SpaceTrajectoryModels
