/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.AdiabaticReactorUniqueness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Chemistry.AdiabaticReactor

-- The unique pair at (a,b,β) = (0,1,1) actually has interior temperature.
example : ∃ p : ℝ × ℝ, IsSteadyState 0 1 1 p ∧ p.2 ∈ Set.Ioo 1 2 ∧
    ∀ q, IsSteadyState 0 1 1 q → q = p := by
  obtain ⟨p, hp, hu⟩ := (steady_state_interval_and_uniqueness 0 (b := 1) (β := 1)
    zero_lt_one zero_le_one).2 (by norm_num)
  refine ⟨p, hp, ?_, hu⟩
  have hz := (((steady_states_and_energy_invariant 0 zero_lt_one zero_le_one).1 p.1 p.2).mp hp).2
  set k := Real.exp (0 - 1 / p.2)
  have hk : 0 < k := Real.exp_pos _
  have hd : 0 < 1 + k := by linarith
  rw [one_mul] at hz
  exact ⟨by linarith only [div_pos hk hd, hz],
    by linarith only [(div_lt_one hd).2 (show k < 1 + k by linarith), hz]⟩

-- At zero feedback, the singleton temperature interval determines T and the balance fixes c.
example (a b : ℝ) (hb : 0 < b) (p : ℝ × ℝ) :
    IsSteadyState a b 0 p ↔ p = (1 / (1 + Real.exp (a - b)), 1) := by
  let q : ℝ × ℝ := (1 / (1 + Real.exp (a - b)), 1)
  have hq : IsSteadyState a b 0 q := by
    apply ((steady_states_and_energy_invariant a hb (le_refl 0)).1 q.1 q.2).mpr
    simp [q]
  obtain ⟨w, _, hu⟩ := (steady_state_interval_and_uniqueness a hb (le_refl 0)).2 (by simp)
  exact ⟨fun hp ↦ (hu p hp).trans (hu q hq).symm, fun he ↦ he ▸ hq⟩

-- At β*b = 4 only the interval clause is being used; it has no product hypothesis.
example (p : ℝ × ℝ) (hp : IsSteadyState 0 4 1 p) : p.2 ∈ Set.Icc 1 2 := by
  simpa only [one_add_one_eq_two] using (steady_state_interval_and_uniqueness 0 (b := 4) (β := 1)
    (by norm_num) zero_le_one).1 p hp
