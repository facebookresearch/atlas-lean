/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Online.ProcessWorkingSet
import Mathlib.Tactic.NormNum

/-!
# Process-time working-set fixtures

A, B, B, C are referenced at process times 3, 4, 4.5, 5 respectively. The process clock
then advances without further references. A separate trace touches infinitely many distinct
pages at process time zero.
-/

namespace Cslib.Algorithms.Lean.Online.Paging

open scoped NNReal

private inductive Page where | a | b | c
  deriving DecidableEq

private def refs (s : ℝ≥0) : Set Page :=
  {p | match p with
    | .a => s = 3
    | .b => s = 4 ∨ s = 9 / 2
    | .c => s = 5}

-- A is on the excluded boundary; C is on the included one. Both references to B count once.
private theorem pagesAtFive : workingSet refs 5 2 = {Page.b, Page.c} := by
  ext p
  cases p <;> norm_num [workingSet, refs, and_or_left, exists_or]

example : workingSetSize refs 5 2 = 2 := by
  rw [workingSetSize, pagesAtFive, Set.encard_pair (by decide)]

private theorem lastB {t : ℝ≥0} (ht : 9 / 2 ≤ t) :
    IsGreatest {u | u ≤ t ∧ Page.b ∈ refs u} (9 / 2) := by
  refine ⟨⟨ht, Or.inr rfl⟩, ?_⟩
  rintro u ⟨_, (rfl | rfl)⟩ <;> norm_num [← NNReal.coe_le_coe]

-- Other pages do not reset B's clock. It is still resident at 6 and expires at 6.5.
example : Page.b ∈ workingSet refs 6 2 := by
  have h : (9 / 2 : ℝ≥0) ≤ 6 := by norm_num [← NNReal.coe_le_coe]
  rw [mem_workingSet_iff_of_isGreatest (lastB h), ← NNReal.coe_lt_coe, NNReal.coe_sub h]
  norm_num

example : Page.b ∉ workingSet refs (13 / 2) 2 := by
  have h : (9 / 2 : ℝ≥0) ≤ 13 / 2 := by norm_num [← NNReal.coe_le_coe]
  rw [mem_workingSet_iff_of_isGreatest (lastB h), ← NNReal.coe_lt_coe, NNReal.coe_sub h]
  norm_num

example : workingSetSize refs 5 0 = 0 := by
  simp [workingSetSize]

-- At time 4 the second B reference and the C reference are still in the future.
example : workingSet refs 4 1 = {Page.b} := by
  ext p
  cases p <;> norm_num [workingSet, refs, and_or_left, exists_or]

private def atOrigin (s : ℝ≥0) : Set ℕ := {_p | s = 0}

-- (−1, 1] contains time zero, and the count must not collapse an infinite set to zero.
private theorem originPages : workingSet atOrigin 1 2 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact ⟨0, by norm_num, rfl⟩

example : workingSetSize atOrigin 1 2 = ⊤ := by
  simp [workingSetSize, originPages]

end Cslib.Algorithms.Lean.Online.Paging
