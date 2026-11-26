/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitions

open MetaMathlibExt

-- At total zero, all three partitions are empty.
example : tripleRegularPartitionCount 2 0 = 1 := kTupleRegularPartitionCount_at_zero 2 3

-- Total two lies strictly between the triangular indices one and three.
example : tripleRegularPartitionCount 2 2 % 2 = 0 := by
  have hn : ¬ ∃ m : ℕ, 2 = m * (m + 1) / 2 := by
    rintro ⟨m, hm⟩
    by_cases h : m < 2
    · have hm' : m = 0 ∨ m = 1 := by omega
      rcases hm' with rfl | rfl <;> omega
    · have hle : 6 ≤ m * (m + 1) :=
        Nat.mul_le_mul (by omega : 2 ≤ m) (by omega : 3 ≤ m + 1)
      omega
  have h := mt (tripleTwo_odd_iff_triangular 2).mp hn
  omega

-- The theorem applies in the odd direction at a positive triangular index.
example : tripleRegularPartitionCount 2 6 % 2 = 1 :=
  (tripleTwo_odd_iff_triangular 6).mpr ⟨3, by decide⟩

-- Conversely, an odd count produces a triangular index.
example (n : ℕ) (h : tripleRegularPartitionCount 2 n % 2 = 1) :
    ∃ m : ℕ, n = m * (m + 1) / 2 :=
  (tripleTwo_odd_iff_triangular n).mp h
