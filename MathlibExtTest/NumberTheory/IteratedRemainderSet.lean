/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IteratedRemainderSet
import Mathlib.Tactic.IntervalCases

/-!
# Tests for iterated remainder sets and the maximal Pierce length
-/

namespace MetaMathlibExt

-- The iterated remainder sets of `5`: `{1, 2}`, `{0, 1}`, `{0}`, then empty.
example : iteratedRemainderSet 0 5 = {1, 2} ∧ iteratedRemainderSet 1 5 = {0, 1} ∧
    iteratedRemainderSet 2 5 = {0} ∧ iteratedRemainderSet 3 5 = ∅ := by
  decide

-- `0` is erased before the next remainders are taken, so it never produces a new element.
example : iteratedRemainderSet 2 4 = ∅ ∧ iteratedRemainderSet 1 4 = {0} := by
  decide

-- An empty iterated remainder set stays empty.
example (n k : ℕ) (h : iteratedRemainderSet k n = ∅) :
    iteratedRemainderSet (k + 1) n = ∅ := by
  simp [iteratedRemainderSet, h]

-- `P(5) = 3`, read off from `S_2(5) = {0}`; the printed index would ask for `S_4(5) = {0}`,
-- but `S_4(5)` is empty.
example : PierceExpansion.maxLength 5 = 3 ∧ iteratedRemainderSet 4 5 = ∅ :=
  ⟨(pierce_maxLength_eq_succ_iff 5 2 (by decide)).1.2 (by decide), by decide⟩

-- `P(35) = 7`, read off from `S_6(35) = {0}`.
example : PierceExpansion.maxLength 35 = 7 :=
  (pierce_maxLength_eq_succ_iff 35 6 (by decide)).1.2 (by decide)

-- The same value through the second characterization: one element, then only empty sets.
example : PierceExpansion.maxLength 35 = 7 := by
  have hstep : ∀ k, iteratedRemainderSet k 35 = ∅ → iteratedRemainderSet (k + 1) 35 = ∅ :=
    fun k h => by simp [iteratedRemainderSet, h]
  refine (pierce_maxLength_eq_succ_iff 35 6 (by decide)).2.2 ⟨by decide, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  induction i with
  | zero => decide
  | succ i ih => exact hstep _ (ih (by omega))

-- The forward direction: `P(n) = t + 1` forces the later sets to be empty.
example (n t : ℕ) (hn : 3 ≤ n) (h : PierceExpansion.maxLength n = t + 1) :
    iteratedRemainderSet t n = {0} ∧ iteratedRemainderSet (t + 1) n = ∅ :=
  ⟨(pierce_maxLength_eq_succ_iff n t hn).1.1 h,
    ((pierce_maxLength_eq_succ_iff n t hn).2.1 h).2 1 le_rfl⟩

-- `S_0(n)` never equals `{0}`, so for `n ≥ 3` the maximal Pierce length is never `1`.
example (n : ℕ) (hn : 3 ≤ n) : PierceExpansion.maxLength n ≠ 1 := by
  intro h
  have h1 : 1 ∈ iteratedRemainderSet 0 n := by
    rw [iteratedRemainderSet, Finset.mem_Icc]
    omega
  rw [(pierce_maxLength_eq_succ_iff n 0 hn).1.1 h, Finset.mem_singleton] at h1
  exact one_ne_zero h1

-- The hypothesis `3 ≤ n` is needed: `P(2) = 0 + 1`, but `S_0(2) = {1}`.
example : PierceExpansion.maxLength 2 = 0 + 1 ∧ iteratedRemainderSet 0 2 ≠ {0} := by
  refine ⟨le_antisymm ?_ ?_, by decide⟩
  · apply PierceExpansion.maxLength_le_of_forall
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨ha1, ha2⟩ := ha
    interval_cases a
    · exact PierceExpansion.length_le_of_traj_eq_zero le_rfl rfl
    · exact PierceExpansion.length_le_of_traj_eq_zero le_rfl rfl
  · exact (PierceExpansion.length_pos 2 1).trans
      (PierceExpansion.length_le_maxLength (by decide))

end MetaMathlibExt
