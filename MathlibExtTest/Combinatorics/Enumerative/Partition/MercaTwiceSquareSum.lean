/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.Partition.MercaTwiceSquareSum

open MetaMathlibExt

-- At `n = 0`, the kernel has no positive index and the progression's only weight is zero.
example : (sumDistinctPartsModEq 1 0 0 : ℤ) = 0 := by
  simpa using sumDistinctPartsModEq_twiceSquare_eq_oddDistinct 1 0 0 (by decide)

private theorem oddDistincts_zero : (Nat.Partition.oddDistincts 0).card = 1 := by
  simp [Nat.Partition.oddDistincts, Nat.Partition.odds, Nat.Partition.distincts,
    Nat.Partition.restricted]

private theorem oddDistincts_two : (Nat.Partition.oddDistincts 2).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  simp only [Nat.Partition.oddDistincts, Nat.Partition.odds, Nat.Partition.distincts,
    Nat.Partition.restricted, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have heq : p.parts = Multiset.replicate p.parts.card 1 := by
    apply Multiset.eq_replicate_card.mpr
    intro i hi
    have hodd := hp.1 i hi
    rw [Nat.even_iff] at hodd
    have := p.parts_pos hi
    have := p.le_of_mem_parts hi
    omega
  have hcard : p.parts.card = 2 := calc
    p.parts.card = (Multiset.replicate p.parts.card (1 : ℕ)).sum := by
      simp [Multiset.sum_replicate, smul_eq_mul]
    _ = p.parts.sum := congrArg Multiset.sum heq.symm
    _ = 2 := p.parts_sum
  have hcount := Multiset.nodup_iff_count_le_one.mp hp.2 1
  rw [heq, Multiset.count_replicate_self, hcard] at hcount
  exact (by decide : ¬ 2 ≤ 1) hcount

-- At `n = 3`, the correction is negative. The gap of 2 counts no distinct odd partition,
-- and the gap of 0 counts the empty partition once, with weight 3.
example : (sumDistinctPartsModEq 2 1 3 : ℤ) - 2 * sumDistinctPartsModEq 2 1 1 = 3 := by
  have h := sumDistinctPartsModEq_twiceSquare_eq_oddDistinct 2 1 3 (by decide)
  rw [show (Finset.Icc 1 3).filter (fun k => 2 * k ^ 2 ≤ 3) = {1} by decide] at h
  norm_num [Finset.sum_filter, Finset.sum_range_succ] at h
  change _ = (Nat.Partition.oddDistincts 2).card +
    (3 : ℤ) * (Nat.Partition.oddDistincts 0).card at h
  norm_num [oddDistincts_zero, oddDistincts_two] at h
  linarith

-- At `n = 9`, the positive shift by `2 * 2²` contributes exactly 2.
example : (sumDistinctPartsModEq 8 1 9 : ℤ) - 2 * sumDistinctPartsModEq 8 1 7 + 2 =
    (Nat.Partition.oddDistincts 8).card + 9 := by
  have h := sumDistinctPartsModEq_twiceSquare_eq_oddDistinct 8 1 9 (by decide)
  have h₁ : sumDistinctPartsModEq 8 1 1 = 1 := by
    norm_num [sumDistinctPartsModEq, Finset.filter_singleton]
  rw [show (Finset.Icc 1 9).filter (fun k => 2 * k ^ 2 ≤ 9) = {1, 2} by decide,
    show (Finset.range 10).filter (fun j => 8 * j + 1 ≤ 9) = {0, 1} by decide] at h
  norm_num [h₁] at h
  change _ = (Nat.Partition.oddDistincts 8).card +
    (9 : ℤ) * (Nat.Partition.oddDistincts 0).card at h
  norm_num [oddDistincts_zero] at h
  linarith
