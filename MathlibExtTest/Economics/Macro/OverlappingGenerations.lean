/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.OverlappingGenerations
import Mathlib.Tactic.NormNum

/-!
# Tests for the two-period OLG capital-market recurrence

With `A = 2`, `β = 1`, `n = 0`: the capital factor is `1/2`, the steady
state is `1/4`, one recurrence step from `k 0 = 1` gives `k 1 = 1/2`, the
optimal savings at wage `3` is `3/2`, and the savings optimum holds at
`w = 3`, `R = 2`, `s = 1` against the optimum `3/2`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.OverlappingGenerations

open MathlibExt.Economics.Macro.OverlappingGenerations

/-- Concrete tests for MA08.T03 with exact values. -/
theorem olgCapitalFactor_value : olgCapitalFactor 2 1 0 = 1 / 2 := by
  unfold olgCapitalFactor
  norm_num

theorem olg_steadyState_value :
    olgCapitalFactor 2 1 0 * Real.sqrt ((olgCapitalFactor 2 1 0) ^ 2) = 1 / 4 := by
  have hC : (0:ℝ) ≤ olgCapitalFactor 2 1 0 := by
    rw [olgCapitalFactor_value]
    norm_num
  have h := olg_steadyState (A := 2) (β := 1) (n := 0) hC
  rw [h, olgCapitalFactor_value]
  norm_num

theorem olg_capitalRecurrence_value {k : ℕ → ℝ} (hk0 : k 0 = 1)
    (hk : ∀ t, k (t + 1) = olgSavings 1 (olgWage 2 (k t)) / (1 + 0)) :
    k 1 = 1 / 2 := by
  have h := olg_capitalRecurrence (A := 2) (β := 1) (n := 0)
    (by norm_num) (by norm_num) hk 0
  rw [hk0, Real.sqrt_one, olgCapitalFactor_value] at h
  norm_num at h
  exact h

theorem olgSavings_value : olgSavings 1 3 = 3 / 2 := by
  unfold olgSavings
  norm_num

theorem logUtility_optimalSavings_value :
    Real.log (3 - 1) + 1 * Real.log (2 * 1) ≤
      Real.log (3 - olgSavings 1 3) + 1 * Real.log (2 * olgSavings 1 3) :=
  logUtility_optimalSavings (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end MathlibExtTest.Economics.Macro.OverlappingGenerations
