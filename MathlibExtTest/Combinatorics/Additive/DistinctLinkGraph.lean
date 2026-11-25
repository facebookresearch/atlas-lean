/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import MathlibExt.Combinatorics.Additive.DistinctLinkGraph

/-! # Tests for distinct link graphs -/

open MetaMathlibExt

private theorem pair_isDistinctSumFreeSet {G : Type*} [Add G] (a b : G) :
    IsDistinctSumFreeSet ({a, b} : Set G) := by
  intro x hx y hy hxy hzx hzy hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with h | h <;> contradiction

-- In `ZMod 3`, the only three-element subset is ruled out by `1 + 2 = 0`.
private theorem maximal_isDistinctSumFreeSet_of_pair {a b : ZMod 3} (hab : a ≠ b) :
    Maximal IsDistinctSumFreeSet ({a, b} : Set (ZMod 3)) := by
  refine ⟨pair_isDistinctSumFreeSet a b, ?_⟩
  intro T hT hsub x hx
  have ha : a ∈ T := hsub (by simp)
  have hb : b ∈ T := hsub (by simp)
  suffices ∀ y ∈ T, y = a ∨ y = b by simpa using this x hx
  intro y hy
  by_contra! hy'
  have residues (z : ZMod 3) : z = 0 ∨ z = 1 ∨ z = 2 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hm (z : ZMod 3) : z ∈ T := by
    have haz := residues a
    have hbz := residues b
    have hyz := residues y
    have hzz := residues z
    have hall : z = a ∨ z = b ∨ z = y := by grind
    rcases hall with rfl | rfl | rfl
    exacts [ha, hb, hy]
  exact hT 1 (hm 1) 2 (hm 2) (by decide) (by decide) (by decide) (hm (1 + 2))

-- The triple `1 + 2 = 0` gives an edge between 0 and 2 when `S = {1}`.
example : Maximal (IsDistinctLinkIndep ({1} : Set (ZMod 3)) {0, 2}) {0} := by
  refine maximal_isDistinctLinkIndep_of_maximal (pair_isDistinctSumFreeSet 0 2) ?_ ?_ ?_ ?_
  · simpa using pair_isDistinctSumFreeSet (1 : ZMod 3) 1
  · simp
    decide
  · simp
  · simpa using maximal_isDistinctSumFreeSet_of_pair (a := 0) (b := 1) (by decide)

-- With both summands in `S`, the same triple gives a loop at 0, so even the empty
-- independent set is maximal when `B = {0}`.
example : Maximal (IsDistinctLinkIndep ({1, 2} : Set (ZMod 3)) {0}) ∅ := by
  refine maximal_isDistinctLinkIndep_of_maximal ?_ (pair_isDistinctSumFreeSet 1 2) ?_ ?_ ?_
  · simpa using pair_isDistinctSumFreeSet (0 : ZMod 3) 0
  · simp
    decide
  · exact Set.empty_subset _
  · simpa using maximal_isDistinctSumFreeSet_of_pair (a := 1) (b := 2) (by decide)
