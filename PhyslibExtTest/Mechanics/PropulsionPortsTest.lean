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
instance, constant mass, and the zero-mass input that the positivity hypothesis excludes.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Linear burn and zero mass
- B. Burn, specific impulse and constant mass

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

end PhyslibExtTest.Mechanics.PropulsionPorts
