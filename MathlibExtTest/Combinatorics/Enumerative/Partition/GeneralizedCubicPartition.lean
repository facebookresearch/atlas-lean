/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Prime.Defs
import MathlibExt.Combinatorics.Enumerative.Partition.GeneralizedCubicPartition

open MetaMathlibExt

-- At `p = 5` the denominator has no `f₂` factor.
example (n : ℕ) : (5 : ℤ) ∣ generalizedCubicPartitionCount 1 (5 * n + 4) :=
  generalizedCubicPartitionCount_prime_five_seven_mod_eight Nat.prime_five (by decide)
    (l := 4) (by decide) n

-- The other residue class gives the congruence modulo seven for three colors.
example (n : ℕ) : (7 : ℤ) ∣ generalizedCubicPartitionCount 3 (7 * n + 4) :=
  generalizedCubicPartitionCount_prime_five_seven_mod_eight Nat.prime_seven (by decide)
    (l := 4) (by decide) n

-- The shift need not be the least representative of its residue class.
example : (7 : ℤ) ∣ generalizedCubicPartitionCount 3 11 :=
  generalizedCubicPartitionCount_prime_five_seven_mod_eight Nat.prime_seven (by decide)
    (l := 11) (by decide) 0

example : generalizedCubicPartitionCount 0 0 = 1 :=
  generalizedCubicPartitionCount_zero 0
