/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitionPrimePower
import MathlibExt.Combinatorics.Enumerative.Partition.NathSaikiaSarmaTripartitionCongruence
meta import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitions

open MetaMathlibExt

-- Compute the count at the first index in the residue class 7 modulo 9 in both APIs.
#guard tripleRegularPartitionCount 2 7 == 120
#guard kTupleRegularPartitionCount 2 3 7 == 120

-- Check the first index for p = t = 5 and j = 1 independently of the theorem.
example : 9 * 5 ^ 2 * 0 + 9 * 5 ^ 2 * 1 / 5 + (57 * 5 ^ 2 - 1) / 8 = 223 := by decide

-- At this literal index, check parity by bounding the neighboring triangular numbers,
-- and divisibility by three using the progression 3 * 74 + 1.
example : Nat.ModEq 6 (tripleRegularPartitionCount 2 223) 0 := by
  have h₂ : Nat.ModEq 2 (tripleRegularPartitionCount 2 223) 0 := by
    change tripleRegularPartitionCount 2 223 % 2 = 0
    by_contra h
    obtain ⟨m, hm⟩ := (tripleTwo_odd_iff_triangular 223).mp (by omega)
    by_cases hb : m ≤ 20
    · have hle : m * (m + 1) ≤ 20 * 21 := Nat.mul_le_mul hb (by omega)
      omega
    · have hle : 21 * 22 ≤ m * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
  have h₃ : Nat.ModEq 3 (tripleRegularPartitionCount 2 223) 0 := by
    rw [tripleRegularPartitionCount_eq_kTupleRegularPartitionCount]
    exact kTupleRegularPartition_primePower_congruent 3 1 2 1 1 1 74
      Nat.prime_three (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 2 3)).mp ⟨h₂, h₃⟩

-- Apply the exported theorem at the same input.
example : Nat.ModEq 6 (tripleRegularPartitionCount 2 223) 0 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hlegendre : legendreSym 5 (-2) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    decide
  exact nathSaikiaSarma_conjecture 5 5 0 1 (by decide) hlegendre (by decide) (by decide)
    (by decide) (by decide) (by decide)
