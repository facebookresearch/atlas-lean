/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitionPrimePower
meta import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitions

open MetaMathlibExt

-- Count at n = 0 on each progression independently of the congruence theorem.
-- The single part 1 can be assigned to any of the three components.
#guard kTupleRegularPartitionCount 2 3 1 == 3
-- At total 3, either one component has all three units, or the sizes split as 2+1 or 1+1+1.
#guard kTupleRegularPartitionCount 3 16 3 == 1072

-- The generating-series coefficient formula is available through the ordinary public import.
example : PowerSeries.coeff 0 (lRegularPartitionSeries ℤ 2 ^ 3) = 1 := by
  rw [coeff_lRegularPartitionSeries_pow, kTupleRegularPartitionCount_at_zero, Nat.cast_one]

-- At α = s = 1 the modulus is the prime itself.
example (n : ℕ) : Nat.ModEq 3 (kTupleRegularPartitionCount 2 3 (3 * n + 1)) 0 :=
  kTupleRegularPartition_primePower_congruent 3 1 2 1 1 1 n
    Nat.prime_three (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- With α > s and m > 1, use the largest allowed residue modulo 2².
example (n : ℕ) : Nat.ModEq 4 (kTupleRegularPartitionCount 3 16 (4 * n + 3)) 0 :=
  kTupleRegularPartition_primePower_congruent 2 2 3 3 2 3 n
    Nat.prime_two (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
