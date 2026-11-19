/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.PropulsionPorts

/-!
# Rocket velocity-increment checks

Concrete consumers of `PhyslibExt.Mechanics.PropulsionPorts`: the linear mass history
`m t = 2 - t` on `[0, 1]` with `ve = 1` (increment, burn and boundary), a specific-impulse
instance, constant mass, and the zero-mass input that the positivity hypothesis excludes; then a
parcel step of the vehicle of mass `2` at rest with flow `1` and exhaust speed `3`, and the parcel
lemmas applied to it and to the burning history `M s = 2 - s`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Linear burn and zero mass
- B. Burn, specific impulse and constant mass
- C. Parcel fixture
- D. Parcel lemmas on the fixture state

## iv. References

None.

## A. Linear burn and zero mass

-/

public section

namespace PhyslibExtTest.Mechanics.PropulsionPorts

open Set PhyslibExt.Mechanics.PropulsionPorts

/-- Derivative data, positivity and the law for the linear burn `m t = 2 - t`,
`v t = log (2 / (2 - t))`, `ve = 1` on `[0, 1]`. -/
lemma linearBurn_data : ∀ t ∈ Icc (0 : ℝ) 1,
    HasDerivAt (fun s : ℝ => 2 - s) (-1) t ∧
    HasDerivAt (fun s : ℝ => Real.log (2 / (2 - s))) (1 / (2 - t)) t ∧
    0 < 2 - t ∧ (2 - t) * (1 / (2 - t)) = -1 * (-1) := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := mem_Icc.mp ht
  have hpos : (0 : ℝ) < 2 - t := by linarith
  have hne : (2 : ℝ) - t ≠ 0 := ne_of_gt hpos
  have hsub : HasDerivAt (fun s : ℝ => 2 - s) (-1) t :=
    (hasDerivAt_id t).const_sub 2
  have hdiv : HasDerivAt (fun s : ℝ => 2 / (2 - s)) ((0 * (2 - t) - 2 * -1) / (2 - t) ^ 2) t :=
    (hasDerivAt_const t (2 : ℝ)).fun_div hsub hne
  have hinner_ne : (2 : ℝ) / (2 - t) ≠ 0 := div_ne_zero (by norm_num) hne
  have hlog := hdiv.log hinner_ne
  have hder_eq : ((0 * (2 - t) - 2 * -1) / (2 - t) ^ 2) / (2 / (2 - t)) = 1 / (2 - t) := by
    field_simp
    ring
  rw [hder_eq] at hlog
  have hlaw : (2 - t) * (1 / (2 - t)) = -1 * (-1) := by
    field_simp
  exact ⟨hsub, hlog, hpos, hlaw⟩

/-- Fixture: `m t = 2 - t` on `[0, 1]` with `ve = 1`. The velocity `v t = log (2 / (2 - t))`
satisfies the law (`m' = -1`, `v' = 1 / (2 - t)`), the mass stays positive, and the increment
`v 1 - v 0` is `1 * log (m 0 / m 1) = log 2 > 0`. -/
example :
    (∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => 2 - s) (-1) t ∧
      HasDerivAt (fun s : ℝ => Real.log (2 / (2 - s))) (1 / (2 - t)) t ∧
      0 < 2 - t ∧ (2 - t) * (1 / (2 - t)) = -1 * (-1)) ∧
    Real.log (2 / (2 - 1)) - Real.log (2 / (2 - 0)) = 1 * Real.log ((2 - 0) / (2 - 1)) ∧
    Real.log (2 / (2 - 1)) - Real.log (2 / (2 - 0)) = Real.log 2 ∧
    0 < Real.log 2 := by
  have hinc := velocity_increment_eq_log (m := fun s : ℝ => 2 - s)
    (v := fun s : ℝ => Real.log (2 / (2 - s))) (m' := fun _ => -1) (v' := fun s => 1 / (2 - s))
    (ve := 1) (tb := 1) zero_le_one (fun t ht => (linearBurn_data t ht).1)
    (fun t ht => (linearBurn_data t ht).2.1) (fun t ht => (linearBurn_data t ht).2.2.1)
    (fun t ht => (linearBurn_data t ht).2.2.2)
  refine ⟨linearBurn_data, hinc, ?_, Real.log_pos (by norm_num)⟩
  norm_num [Real.log_one]

/-- Zero mass is excluded: with `m ≡ 0`, `ve = 1` and `v t = t` on `[0, 1]` the derivative data
and the law `0 * 1 = -1 * 0` hold, yet the increment `1 - 0` differs from
`1 * log (0 / 0) = 0`. Positivity of the mass cannot be dropped. -/
example :
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t ∧
      HasDerivAt (fun s : ℝ => s) 1 t ∧ (0 : ℝ) * 1 = -1 * 0) ∧
    (1 : ℝ) - 0 ≠ 1 * Real.log (0 / 0) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    refine ⟨hasDerivAt_const t 0, hasDerivAt_id t, by norm_num⟩
  · simp

/-! ## B. Burn, specific impulse and constant mass -/

/-- The linear burn expels mass (`m 1 = 1 < 2 = m 0`), so its increment is positive. -/
example : 0 < Real.log (2 / (2 - 1)) - Real.log (2 / (2 - 0)) := by
  have hb := velocity_increment_burn_and_boundary (m := fun s : ℝ => 2 - s)
    (v := fun s : ℝ => Real.log (2 / (2 - s))) (m' := fun _ => -1) (v' := fun s => 1 / (2 - s))
    (ve := 1) (tb := 1) zero_le_one one_pos (fun t ht => (linearBurn_data t ht).1)
    (fun t ht => (linearBurn_data t ht).2.1) (fun t ht => (linearBurn_data t ht).2.2.1)
    (fun t ht => (linearBurn_data t ht).2.2.2) (fun x _ y _ hxy => by simp only; linarith)
  exact hb.2.2.mpr (by norm_num)

/-- Specific impulse at a burning instant: mass `1000`, velocity rate `6`, mass rate `-2` and
exhaust speed `3000` satisfy the law (`6000 = 6000`); with `g0 = 10` the impulse is `300`. -/
example : specificImpulse (1000 * 6) (-(-2)) 10 = 300 := by
  have h := specificImpulse_eq_of_law (m := fun _ : ℝ => 1000) (v' := fun _ => 6)
    (m' := fun _ => -2) (ve := 3000) (g0 := 10) (t := 0) (by norm_num) (by norm_num)
    (by norm_num)
  rw [h]
  norm_num

/-- With constant mass `5` the law forces zero velocity rate, so any velocity history obeying it
on `[0, 1]` ends where it starts. -/
example (v v' : ℝ → ℝ) (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (v' t) t)
    (hlaw : ∀ t ∈ Icc (0 : ℝ) 1, 5 * v' t = -3 * 0) : v 1 = v 0 :=
  velocity_increment_const_mass zero_le_one (by norm_num) hv hlaw


/-! ## C. Parcel fixture -/

open Filter Topology PhyslibExt.Mechanics.PowerPorts

/-- `m = 2`, `v = 0`, `q = 1`, `ve = 3`, `F = 0`: the step `h = 1 / 2` gives `v_h = 1` (momentum
`(3 / 2) · 1 + (1 / 2) · (-3) = 0`), the slope tends to `3 / 2`, and the balance without the
expelled momentum predicts no acceleration at all. -/
example :
    parcelVelocity 2 0 1 3 0 (1 / 2) = 1 ∧
      Tendsto (fun h => (parcelVelocity 2 0 1 3 0 h - 0) / h) (𝓝[≠] 0) (𝓝 (3 / 2)) ∧
      Tendsto (fun h => (naiveParcelVelocity 2 0 1 0 h - 0) / h) (𝓝[≠] 0) (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold parcelVelocity
    norm_num
  · have h := parcel_slope_tendsto (show (0 : ℝ) < 2 by norm_num) 0 1 3 0
    have heq : ((3 : ℝ) * 1 + 0) / 2 = 3 / 2 := by norm_num
    rwa [heq] at h
  · have h := naive_slope_tendsto (show (0 : ℝ) < 2 by norm_num) 0 1 0
    have heq : ((1 : ℝ) * 0 + 0) / 2 = 0 := by norm_num
    rwa [heq] at h

/-! ## D. Parcel lemmas on the fixture state -/

/-- The fixture step `h = 1 / 2` satisfies the parcel momentum balance. -/
example : (2 - 1 * (1 / 2)) * parcelVelocity 2 0 1 3 0 (1 / 2) + 1 * (1 / 2) * (0 - 3) =
    2 * 0 + 0 * (1 / 2) :=
  (parcel_momentum_iff (by norm_num) 0 3 0 _).mpr rfl

/-- The linear burning history `M s = 2 - s` at `t = 0` expels mass at the constant actual rate
`1`, so the constant-flow step is the actual step; with `ve = 3` and `F = 0` its slope tends to
`3 / 2`. -/
example : (∀ h : ℝ, h ≠ 0 → (2 - (2 - h)) / h = 1) ∧
    Tendsto (fun h => (parcelVelocity 2 0 1 3 0 h - 0) / h) (𝓝[≠] 0) (𝓝 (3 / 2)) := by
  obtain ⟨h₁, h₂⟩ := parcel_continuum_linear (M := fun s : ℝ => 2 - s) (m' := -1) (t := 0)
    (fun h => by ring) (by norm_num) 0 3 0
  exact ⟨fun h hh => by simpa using h₁ h hh, by simpa using h₂⟩

/-- The nonlinear history `M s = 2 - s - s ^ 2` at `t = 0`, with `M' 0 = -1`: the parcel step with
the actual flow `q_h = 1 + h` leaves exactly the mass `M h` for small `h ≠ 0`, and with `ve = 3`,
`F = 0` its slope tends to `3 / 2`. The constant flow `1` would leave `2 - h` instead: at
`h = 1 / 2`, `3 / 2` against `M (1 / 2) = 5 / 4`. -/
example :
    (∀ᶠ h in 𝓝[≠] (0 : ℝ), 2 - (2 - (2 - h - h ^ 2)) / h * h = 2 - h - h ^ 2) ∧
      Tendsto (fun h => (parcelVelocity 2 0 ((2 - (2 - h - h ^ 2)) / h) 3 0 h - 0) / h)
        (𝓝[≠] 0) (𝓝 (3 / 2)) ∧
      (2 : ℝ) - 1 * (1 / 2) ≠ 2 - 1 / 2 - (1 / 2) ^ 2 := by
  have hM : HasDerivAt (fun s : ℝ => 2 - s - s ^ 2) (-1) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_sub 2).fun_sub (hasDerivAt_pow 2 (0 : ℝ))
  obtain ⟨-, h₂, h₃⟩ := parcel_continuum hM (by norm_num) 0 3 0
  refine ⟨?_, by simpa using h₃, by norm_num⟩
  filter_upwards [h₂] with h hh
  simpa using hh.1

/-- Without expelled mass the parcel step of the fixture vehicle under the force `4` is the
fixed-mass velocity `0 + (1 / 2) / 2 · 4 = 1`. -/
example : parcelVelocity 2 0 0 3 4 (1 / 2) = constForceVelocity 2 0 4 (1 / 2) :=
  parcelVelocity_zero_flow (by norm_num) 0 3 4 (1 / 2)

/-- The fixture flow accelerates the vehicle, and ignoring the expelled momentum misses it. -/
example : 0 < ((3 : ℝ) * 1 + 0) / 2 ∧ ((1 : ℝ) * 0 + 0) / 2 ≠ (3 * 1 + 0) / 2 :=
  ⟨parcel_accel_pos (by norm_num) (by norm_num) (by norm_num) rfl,
    naive_limit_ne (by norm_num) (by norm_num) (by norm_num) 0⟩

end PhyslibExtTest.Mechanics.PropulsionPorts
