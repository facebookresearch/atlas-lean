/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Ideal variable-mass logarithmic velocity increment

Reduced collinear model of an ideal rocket burn on `[0, tb]`: positive mass `m`, velocity `v`,
constant exhaust speed `ve > 0` relative to the vehicle, directed backward, and the declared law
`m t * v' t = -ve * m' t` (thrust equals mass flow `-m'` times exhaust speed).

## i. Overview

No external force (gravity, drag) acts in this law, and it is a stated model input, not a
consequence of a fixed-mass Newtonian system. Integrating it gives the ideal rocket equation
`v tb - v 0 = ve * log (m 0 / m tb)`. For nonincreasing mass the increment is nonnegative, zero
exactly at equal end masses and positive exactly for a nonzero burn; constant mass gives no
increment. In this pressure-matched model (no pressure-thrust term) the specific impulse is
`ve / g0`, with `g0 > 0` the reference acceleration used to quote `Isp` in seconds, not
necessarily local gravity. Signs: `m' < 0` during a burn, so `v' = -ve * m' / m > 0`.

## ii. Key results

- `velocity_increment_eq_log`: the ideal rocket equation from the reduced law.
- `velocity_increment_burn_and_boundary`: nonnegative increment, zero exactly at equal end
  masses, positive exactly for a nonzero burn.
- `specificImpulse_eq_of_law`: `Isp = ve / g0` at any burning instant.
- `velocity_increment_const_mass`: constant positive mass gives zero increment.

## iii. Table of contents

- A. Integrated velocity increment
- B. Specific impulse
- C. Constant mass

## iv. References

- G. P. Sutton and O. Biblarz, *Rocket Propulsion Elements*, 9th edition, chapters 2 and 4
  (specific impulse, effective exhaust velocity, ideal rocket equation).
- H. D. Curtis, *Orbital Mechanics for Engineering Students*, rocket vehicle dynamics chapter.
-/

@[expose] public section

namespace PhyslibExt.Mechanics.PropulsionPorts

open Set

/-! ## A. Integrated velocity increment -/

/-- Ideal rocket equation from the reduced variable-mass law. For mass `m` and velocity `v`
with derivatives `m'`, `v'` on `[0, tb]` (continuous there, so both are `C¹`), positive mass,
constant `ve > 0` and `m * v' = -ve * m'` on `[0, tb]`, the velocity increment is
`ve * log (m 0 / m tb)`. The identity does not use `ve > 0` or the continuity of the
derivatives (those binders are underscored); they are kept as the contracted model class. -/
lemma velocity_increment_eq_log {m v m' v' : ℝ → ℝ} {ve tb : ℝ} (htb : 0 ≤ tb) (_hve : 0 < ve)
    (hm : ∀ t ∈ Icc 0 tb, HasDerivAt m (m' t) t) (hv : ∀ t ∈ Icc 0 tb, HasDerivAt v (v' t) t)
    (_hm'c : ContinuousOn m' (Icc 0 tb)) (_hv'c : ContinuousOn v' (Icc 0 tb))
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

/-- Nonincreasing mass admits both cases: the increment is nonnegative, zero exactly when the
end masses are equal (no net burn), and positive exactly when mass was expelled. -/
lemma velocity_increment_burn_and_boundary {m v m' v' : ℝ → ℝ} {ve tb : ℝ} (htb : 0 ≤ tb)
    (hve : 0 < ve) (hm : ∀ t ∈ Icc 0 tb, HasDerivAt m (m' t) t)
    (hv : ∀ t ∈ Icc 0 tb, HasDerivAt v (v' t) t) (hm'c : ContinuousOn m' (Icc 0 tb))
    (hv'c : ContinuousOn v' (Icc 0 tb)) (hpos : ∀ t ∈ Icc 0 tb, 0 < m t)
    (hlaw : ∀ t ∈ Icc 0 tb, m t * v' t = -ve * m' t) (hanti : AntitoneOn m (Icc 0 tb)) :
    0 ≤ v tb - v 0 ∧ (v tb - v 0 = 0 ↔ m tb = m 0) ∧ (0 < v tb - v 0 ↔ m tb < m 0) := by
  have hmain := velocity_increment_eq_log htb hve hm hv hm'c hv'c hpos hlaw
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

end PhyslibExt.Mechanics.PropulsionPorts
