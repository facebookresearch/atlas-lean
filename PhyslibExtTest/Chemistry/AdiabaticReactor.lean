/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.AdiabaticReactor
import Mathlib.Tactic.NormNum

open Chemistry.AdiabaticReactor

-- At unit temperature the chosen Arrhenius rate is one. With no heat release,
-- the steady state therefore has concentration one half and temperature one.
example : (1 : ℝ) - 1 / 2 - Real.exp (1 - 1 / 1) * (1 / 2) = 0 ∧
    (1 : ℝ) - 1 + 0 * Real.exp (1 - 1 / 1) * (1 / 2) = 0 := by
  apply ((steady_states_and_energy_invariant 1 (b := 1) (β := 0)
    zero_lt_one le_rfl).1 (1 / 2) 1).mpr
  norm_num

-- Nonzero heat release and an initial temperature below the feed temperature.
-- The ceiling is three even when the Arrhenius prefactor is exp 2.
example : ∃ c T : ℝ → ℝ, c 0 = 1 / 2 ∧ T 0 = 1 / 2 ∧ ∀ t ≥ 0,
    c t ∈ Set.Icc 0 1 ∧ T t ∈ Set.Icc (1 / 2) 3 := by
  have hc : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
  obtain ⟨c, T, hc0, hT0, h⟩ :=
    (steady_states_and_energy_invariant 2 (b := 1) (β := 2) zero_lt_one (by norm_num)).2.2
      hc (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨c, T, hc0, hT0, fun t ht ↦ ⟨(h t ht).1, ?_⟩⟩
  have hlo : min (1 / 2 : ℝ) 1 = 1 / 2 := min_eq_left (by norm_num)
  have hhi : max (1 / 2 + 2 * (1 / 2) : ℝ) (1 + 2) = 3 := by
    rw [max_eq_right (by norm_num : (1 / 2 + 2 * (1 / 2) : ℝ) ≤ 1 + 2)]
    norm_num
  simpa only [hlo, hhi] using (h t ht).2.1
