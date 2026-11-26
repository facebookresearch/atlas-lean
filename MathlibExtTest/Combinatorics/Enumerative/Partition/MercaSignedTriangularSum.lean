/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.Partition.MercaSignedTriangularSum

open MetaMathlibExt

-- At index zero the gap is even but the weight is zero; the positive part size leaves an odd gap.
example :
    ∑ k ∈ (Finset.range 5).filter (fun k => k * (k + 1) / 2 ≤ 4),
      (-1 : ℤ) ^ (k * (k + 1) / 2) * (sumDistinctPartsModEq 3 0 (4 - k * (k + 1) / 2) : ℤ) = 0 := by
  rw [sumDistinctPartsModEq_triangular_eq_distinct_half 3 0 4 (by decide)]
  norm_num [Finset.sum_filter, Finset.sum_range_succ, Nat.even_iff]

-- The odd gap at part size 1 vanishes, while the gap of 2 at part size 4 counts the partition of 1.
example :
    ∑ k ∈ (Finset.range 7).filter (fun k => k * (k + 1) / 2 ≤ 6),
      (-1 : ℤ) ^ (k * (k + 1) / 2) * (sumDistinctPartsModEq 3 1 (6 - k * (k + 1) / 2) : ℤ) = 4 := by
  rw [sumDistinctPartsModEq_triangular_eq_distinct_half 3 1 6 (by decide)]
  norm_num [Finset.sum_filter, Finset.sum_range_succ, Nat.even_iff, Nat.Partition.distincts]
