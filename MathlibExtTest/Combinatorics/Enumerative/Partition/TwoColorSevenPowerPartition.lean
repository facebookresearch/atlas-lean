/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.TwoColorSevenPowerPartition

open MetaMathlibExt

-- A ceiling in the exponent would incorrectly require seven to divide this entry.
example : garvanM 2 1 = 10 ∧ ¬ 7 ∣ garvanM 2 1 := by decide

-- A negative numerator occurs even at a nonzero entry.
example : garvanM 7 2 = 1 := by decide

-- The table ends at column fourteen, and the recurrence starts in column three.
example : garvanM 7 14 = 7 ^ 20 ∧ garvanM 7 15 = 0 ∧ garvanM 8 2 = 0 := by decide

-- All three shifted bounds apply to nonzero entries beyond the initial rows.
example : 7 ^ 4 ∣ garvanM 8 5 ∧ 7 ^ 4 ∣ garvanM 9 5 ∧ 7 ^ 3 ∣ garvanM 10 5 :=
  (seven_pow_dvd_garvanM 2 3 (by decide) (by decide)).2

-- At the first allowed multiple the second color gives one extra partition.
example : twoColorMultiplePartitionCount 1 1 = 2 := by
  simp [twoColorMultiplePartitionCount, Finset.sum_range_succ]

-- On their first recursive step the odd and even vectors use different rows of the matrix.
example :
    garvanYOdd 1 2 1 = 7 * garvanM 5 2 + 49 * garvanM 9 3 ∧
    garvanYEven 1 2 1 = 7 * garvanM 4 2 + 49 * garvanM 8 3 := by decide

-- The bound is sharp in the first column of the first even vector.
example : 49 ∣ garvanX 2 1 ∧ ¬ 343 ∣ garvanX 2 1 :=
  ⟨(seven_pow_dvd_garvanX 1 1 (by decide) (by decide)).2.2.2, by decide⟩

-- At the third column, the odd and even bounds differ by a factor of seven.
example :
    padicValNat 7 (garvanX 1 1) = 1 ∧ padicValNat 7 (garvanX 1 2) = 2 ∧
      7 ^ 7 ∣ garvanX 5 3 ∧ 7 ^ 6 ∣ garvanX 4 3 :=
  seven_pow_dvd_garvanX (k := 2) (j := 3) (hk := by decide) (hj := by decide)

-- The second entry of the first odd vector attains the bound; the third is zero.
example : 7 ^ 2 ∣ garvanYOdd 1 1 2 ∧ ¬ 7 ^ 3 ∣ garvanYOdd 1 1 2 :=
  ⟨seven_pow_dvd_garvanYOdd 1 0 2 (by decide) (by decide), by decide⟩

example : garvanYOdd 1 1 3 = 0 := by decide

-- With k > 1 the initial bound comes from a later odd Garvan x vector.
example : 7 ^ 5 ∣ garvanYOdd 2 1 3 :=
  seven_pow_dvd_garvanYOdd 2 0 3 (by decide) (by decide)

-- After one recurrence step the first column is still sharp, and column two gains a factor.
example : 7 ∣ garvanYOdd 1 2 1 ∧ ¬ 7 ^ 2 ∣ garvanYOdd 1 2 1 ∧ 7 ^ 2 ∣ garvanYOdd 1 2 2 :=
  ⟨seven_pow_dvd_garvanYOdd 1 1 1 (by decide) (by decide), by decide,
    seven_pow_dvd_garvanYOdd 1 1 2 (by decide) (by decide)⟩
