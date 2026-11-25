/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Testing.Generators
import Mathlib.Tactic.NormNum

/-! # Tests -/

@[expose] public section

namespace Cslib.Testing

theorem sortedNatLists_zero : sortedNatLists 0 = {[]} := by
  decide

theorem sortedNatLists_two :
    sortedNatLists 2 = {[], [0], [1], [0, 0]} := by
  decide

theorem one_zero_not_mem_sortedNatLists_two : [1, 0] ∉ sortedNatLists 2 := by
  decide

theorem two_not_mem_sortedNatLists_two : [2] ∉ sortedNatLists 2 := by
  decide

theorem two_mem_sortedNatLists_three : [2] ∈ sortedNatLists 3 := by
  decide

theorem one_one_mem_sortedNatLists_three : [1, 1] ∈ sortedNatLists 3 := by
  decide

theorem sum_le_one_of_mem_sortedNatLists_two {xs : List ℕ}
    (hxs : xs ∈ sortedNatLists 2) : xs.sum ≤ 1 := by
  rw [sortedNatLists_two] at hxs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl <;> decide

theorem not_forall_sorted_sum_le_one :
    ¬ ∀ xs : List ℕ, xs.Pairwise (· ≤ ·) → xs.sum ≤ 1 := by
  intro h
  have h2 := h [2] (by simp)
  simp at h2

theorem not_forall_mem_sortedNatLists_two_sum_eq_zero :
    ¬ ∀ xs ∈ sortedNatLists 2, xs.sum = 0 := by
  intro h
  have hmem : [1] ∈ sortedNatLists 2 := by decide
  have h1 := h [1] hmem
  simp at h1

end Cslib.Testing
