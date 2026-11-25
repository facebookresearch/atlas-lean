/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Finpartition.PairMerge

/-! # Tests for the uniform pair-merger walk -/

@[expose] public section

open Finset Finpartition

/-- With just two singleton blocks there is exactly one successor. -/
example : pairMergeMatrix (univ : Finset Bool) ⊥ ⊤ = 1 := by
  have h : IsPairMerge (⊥ : Finpartition (univ : Finset Bool)) ⊤ := by
    exact ⟨bot_le, by decide⟩
  rw [pairMergeMatrix_of_merge (by decide) h]
  norm_num [show #(⊥ : Finpartition (univ : Finset Bool)).parts = 2 by decide, Nat.choose_self]

/-- Any given merger from three blocks has probability `1 / 3`, not probability one. -/
example {α : Type*} [DecidableEq α] {s : Finset α} {P Q : Finpartition s}
    (hP : #P.parts = 3) (h : IsPairMerge P Q) : pairMergeMatrix s P Q = 1 / 3 := by
  rw [pairMergeMatrix_of_merge (by omega) h, hP]
  norm_num [Nat.choose]

/-- An empty partition has no possible pair but still has a transition of mass one. -/
example : pairMergeMatrix (∅ : Finset ℕ) ⊥ ⊥ = 1 := by
  apply pairMergeMatrix_self_of_lt_two
  simp
