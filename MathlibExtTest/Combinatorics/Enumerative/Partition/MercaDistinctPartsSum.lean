/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.MercaDistinctPartsSum

open MetaMathlibExt

-- No part in this residue class fits in a partition of n.
example (m r n : ℕ) (hrm : r < m) (hnr : n < r) : sumDistinctPartsModEq m r n = 0 := by
  rw [sumDistinctPartsModEq_eq_sum_partition m r n hrm]
  apply Finset.sum_eq_zero
  intro j hj
  have := (Finset.mem_filter.mp hj).2
  omega

-- The partition 1 + 1 contributes its repeated part only once.
example : sumDistinctPartsModEq 2 1 2 = 1 := by
  rw [sumDistinctPartsModEq_eq_sum_partition 2 1 2 (by decide)]
  simp [Finset.sum_filter, Finset.sum_range_succ]

-- The full residue class includes the endpoint 2 and a zero-weight term at 0.
example : sumDistinctPartsModEq 1 0 2 = 3 := by
  rw [sumDistinctPartsModEq_eq_sum_partition 1 0 2 (by decide)]
  simp [Finset.sum_filter, Finset.sum_range_succ]

example (m : ℕ) : sumDistinctPartsMultAtLeast m 0 = 0 := by
  simp [sumDistinctPartsMultAtLeast]

-- The partitions (2) and (1,1) contribute 2 and 1 respectively.
example : sumDistinctPartsMultAtLeast 1 2 = 3 := by
  rw [sumDistinctPartsMultAtLeast_eq_sum_partition 1 2 (by decide)]
  simp [Finset.sum_filter, Finset.sum_range_succ]

-- Only (1,1,1) meets this threshold, and its part 1 contributes once.
example : sumDistinctPartsMultAtLeast 2 3 = 1 := by
  rw [sumDistinctPartsMultAtLeast_eq_sum_partition 2 3 (by decide)]
  simp [Finset.sum_filter, Finset.sum_range_succ]

example {m n : ℕ} (h : n < m) : sumDistinctPartsMultAtLeast m n = 0 := by
  rw [sumDistinctPartsMultAtLeast_eq_sum_partition m n (by omega)]
  apply Finset.sum_eq_zero
  intro j hj
  obtain rfl | hjpos := Nat.eq_zero_or_pos j
  · simp
  · have hmj := Nat.le_mul_of_pos_right m hjpos
    exact (h.not_ge (hmj.trans (Finset.mem_filter.mp hj).2)).elim
