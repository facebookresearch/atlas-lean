/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitionPrimePower

open MetaMathlibExt

-- At α = s = 1 the modulus is the prime itself.
example (n : ℕ) : Nat.ModEq 3 (kTupleRegularPartitionCount 2 3 (3 * n + 1)) 0 :=
  kTupleRegularPartition_primePower_congruent 3 1 2 1 1 1 n
    Nat.prime_three (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- With α > s and m > 1, use the largest allowed residue modulo 2².
example (n : ℕ) : Nat.ModEq 4 (kTupleRegularPartitionCount 3 16 (4 * n + 3)) 0 :=
  kTupleRegularPartition_primePower_congruent 2 2 3 3 2 3 n
    Nat.prime_two (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
