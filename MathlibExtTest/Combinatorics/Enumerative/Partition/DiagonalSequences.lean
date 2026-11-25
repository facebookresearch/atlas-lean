/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.DiagonalSequences

namespace MetaMathlibExt

-- The empty partition has no columns, for any choice of the multiplicities.
example (s : ℕ → ℕ) : conjugateParts ↑(diagonalMaxPartition 0 s) = 0 :=
  conjugateParts_diagonalMaxPartition 0 s

-- The gaps in the paper's four-row example include both a unit gap and repeated column heights.
example : conjugateParts ↑([8, 6, 4, 3] : List ℕ) = ↑([4, 4, 4, 3, 2, 2, 1, 1] : List ℕ) := by
  simpa only [diagonalMaxPartition_four_example, diagonalMinPartition_four_example] using
    conjugateParts_diagonalMaxPartition 4 (fun k => [0, 1, 1, 0, 2].getD k 0)

-- Adding a cell to the empty staircase gives a singleton class.
example (p : Nat.Partition 1) : (diagonalClass p).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨p, Finset.ext fun q => ?_⟩
  obtain rfl := Subsingleton.elim q p
  simp [mem_diagonalClass_self]

-- The row and column of size two have the same sequence, including the trailing zeros.
example : Nat.Partition.ofMultiset {1, 1} ∈ diagonalClass (Nat.Partition.indiscrete 2) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, funext fun k => ?_⟩
  change diagonalSequence {1, 1} k = diagonalSequence {2} k
  match k with
  | 0 | 1 | 2 => decide
  | j + 3 =>
    unfold diagonalSequence
    have hempty (s : Multiset ℕ) (hs : s = {1, 1} ∨ s = {2}) :
        ((Finset.Icc 1 (j + 3)).filter fun i => i ≤ s.countP (j + 3 + 1 - i ≤ ·)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi
      have := Finset.mem_Icc.mp hi
      rcases hs with rfl | rfl <;>
        simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.countP_cons,
          Multiset.countP_zero] <;> split_ifs <;> omega
    rw [hempty _ (Or.inl rfl), hempty _ (Or.inr rfl)]

-- The square and the single row of size four differ on the second diagonal.
example : Nat.Partition.ofMultiset {2, 2} ∉ diagonalClass (Nat.Partition.indiscrete 4) := by
  classical
  intro h
  have heq := congrFun (Finset.mem_filter.mp h).2 2
  exact (by decide : diagonalSequence {2, 2} 2 ≠ diagonalSequence {4} 2) heq

end MetaMathlibExt
