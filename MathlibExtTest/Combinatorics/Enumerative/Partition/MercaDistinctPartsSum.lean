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
