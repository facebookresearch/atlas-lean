/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZeckendorfOdometer
import Mathlib.Tactic.IntervalCases

open MetaMathlibExt

-- With the shortest block, a nonzero infinite tail starts immediately above the zero window.
-- Its first one survives adding the low digit and the block.
example :
    let x := fun i : ℕ => decide (10 ≤ i ∧ i % 2 = 0)
    zeckOdometer^[19] x 9 = false ∧ zeckOdometer^[19] x 10 = true := by
  intro x
  have hx : x ∈ zeckAdic := by
    refine ⟨rfl, rfl, fun i => ?_⟩
    simp only [x, decide_eq_false_iff_not]
    omega
  have hr : Nat.zeckendorf 74 = [10, 7, 5, 2] :=
    Nat.zeckendorf_sum_fib (l := [10, 7, 5, 2]) (by unfold List.IsZeckendorfRep; decide)
  have h := zeckOdometer_stopping_block hx (ℓ := 2) (m := 0) (r := 74) le_rfl
    (by decide) (by rw [hr]; decide) (by rw [hr]; decide)
    (by intro i hi; rw [hr]; interval_cases i <;> decide)
  rw [hr] at h
  exact ⟨(h.1 9 (by decide)).1.trans (h.1 9 (by decide)).2,
    (h.1 10 (by decide)).1.trans (h.1 10 (by decide)).2⟩

-- The next block length allows a one in the interior at index 6. Both inputs also have
-- a one at index 12, so adding the high part creates a carry above the window.
example :
    let x := fun i : ℕ => decide (i = 6 ∨ i = 12)
    zeckOdometer^[197] x 6 = zeckOdometer^[53] x 6 := by
  intro x
  have hx : x ∈ zeckAdic := by
    refine ⟨rfl, rfl, fun i => ?_⟩
    simp only [x, decide_eq_false_iff_not]
    omega
  have hr : Nat.zeckendorf 197 = [12, 9, 7, 5, 2] :=
    Nat.zeckendorf_sum_fib (l := [12, 9, 7, 5, 2]) (by unfold List.IsZeckendorfRep; decide)
  have h := zeckOdometer_stopping_block hx (ℓ := 2) (m := 1) (r := 197) le_rfl
    (by decide) (by rw [hr]; decide) (by rw [hr]; decide)
    (by intro i hi; rw [hr]; interval_cases i <;> decide)
  rw [hr] at h
  exact h.2 6 (by decide) (by decide)
