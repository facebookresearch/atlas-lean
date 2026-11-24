/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.ExtremalDiagonalSequences
import MathlibExt.Combinatorics.Enumerative.Partition.RepeatedPartsDiagonalSequences
import Mathlib.Data.List.GetD

namespace MetaMathlibExt

-- A partition with distinct parts is the maximal partition of its diagonal class.
example {n : ℕ} (p : Nat.Partition n) (q : ℕ) (s : ℕ → ℕ)
    (hd : diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q s))
    (hp : p.parts.Nodup) : p.parts.sort (· ≥ ·) = diagonalMaxPartition q s := by
  by_contra hne
  obtain ⟨i, hi, heq⟩ := (exists_eq_succ_of_ne_diagonalMaxPartition p q s hd).1 hne
  have hnd : (p.parts.sort (· ≥ ·)).Nodup := by
    rw [← Multiset.coe_nodup, Multiset.sort_eq]
    exact hp
  have hlen : (p.parts.sort (· ≥ ·)).length = p.parts.card := Multiset.length_sort _
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
  have := hnd.getElem_inj_iff.mp heq
  omega

-- The paper's running example: q = 4 and s = (1, 1, 0, 2), with diagonal sequence
-- (1, 2, 3, 4, 4, 4, 2, 1).
private def exampleMultiplicities : ℕ → ℕ := fun k => [0, 1, 1, 0, 2].getD k 0

-- Sorting a weakly decreasing list of parts returns the list.
private theorem sort_coe_of_pairwise {l : List ℕ} (h : l.Pairwise (· ≥ ·)) :
    (l : Multiset ℕ).sort (· ≥ ·) = l :=
  List.mergeSort_eq_self _ h

-- The minimal partition (4, 4, 4, 3, 2, 2, 1, 1) of the example class.
private def minExample : Nat.Partition 21 where
  parts := ↑(diagonalMinPartition 4 exampleMultiplicities)
  parts_pos := by decide
  parts_sum := by decide

-- The maximal partition (8, 6, 4, 3) of the example class.
private def maxExample : Nat.Partition 21 where
  parts := ↑(diagonalMaxPartition 4 exampleMultiplicities)
  parts_pos := by decide
  parts_sum := by decide

-- The minimal partition is not maximal, so two of its consecutive parts agree.
example : ∃ i, i + 1 < minExample.parts.card ∧
    (minExample.parts.sort (· ≥ ·)).getD i 0 =
      (minExample.parts.sort (· ≥ ·)).getD (i + 1) 0 :=
  (exists_eq_succ_of_ne_diagonalMaxPartition minExample 4 exampleMultiplicities
    (diagonalSequence_max_eq_min_and_multiset 4 exampleMultiplicities).2.1).1 (by
      rw [show minExample.parts.sort (· ≥ ·) = diagonalMinPartition 4 exampleMultiplicities from
        sort_coe_of_pairwise (by decide)]
      decide)

-- The maximal partition is not minimal, so two of its consecutive parts differ by at least two.
example : ∃ i, i < maxExample.parts.card ∧
    (maxExample.parts.sort (· ≥ ·)).getD (i + 1) 0 + 1 <
      (maxExample.parts.sort (· ≥ ·)).getD i 0 :=
  (exists_eq_succ_of_ne_diagonalMaxPartition maxExample 4 exampleMultiplicities
    ((diagonalSequence_max_eq_min_and_multiset 4 exampleMultiplicities).1.trans
      (diagonalSequence_max_eq_min_and_multiset 4 exampleMultiplicities).2.1)).2 (by
      rw [show maxExample.parts.sort (· ≥ ·) = diagonalMaxPartition 4 exampleMultiplicities from
        sort_coe_of_pairwise (by decide)]
      decide)

end MetaMathlibExt
