/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.RookThreeRecurrence
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

open PowerSeries

-- The first index covered by the homogeneous recurrence.
example : (maxRookPartitionCount 3 15 : ℤ) =
    2 * maxRookPartitionCount 3 14 - maxRookPartitionCount 3 13 +
      maxRookPartitionCount 3 12 - 2 * maxRookPartitionCount 3 11 +
      maxRookPartitionCount 3 10 :=
  maxRookPartitionCount_three_recurrence (n := 15) (hn := by decide)

-- Immediately below the cutoff, the degree-fourteen numerator term contributes one.
example : (maxRookPartitionCount 3 14 : ℤ) -
    (2 * maxRookPartitionCount 3 13 - maxRookPartitionCount 3 12 +
      maxRookPartitionCount 3 11 - 2 * maxRookPartitionCount 3 10 +
      maxRookPartitionCount 3 9) = 1 := by
  let F := mk fun k ↦ (maxRookPartitionCount 3 k : ℤ)
  have h : F - 2 • (X ^ 1 * F) + X ^ 2 * F - X ^ 3 * F + 2 • (X ^ 4 * F) - X ^ 5 * F =
      X ^ 6 + 2 • X ^ 7 + X ^ 8 + 2 • X ^ 9 - X ^ 10 - X ^ 12 - X ^ 13 + X ^ 14 := by
    calc
      _ = (1 - X) ^ 3 * (1 + X + X ^ 2) * F := by ring
      _ = _ := by rw [maxRookPartitionCount_three_genFun]; ring
  have hs (k : ℕ) (hk : k ≤ 5) :
      coeff 14 (X ^ k * F) = (maxRookPartitionCount 3 (14 - k) : ℤ) := by
    rw [coeff_X_pow_mul', ite_eq_left (by omega : k ≤ 14), coeff_mk]
  have hz (k : ℕ) (hk : k < 14) : coeff 14 ((X : ℤ⟦X⟧) ^ k) = 0 := by
    rw [coeff_X_pow, ite_eq_right (by omega)]
  have hc := congrArg (coeff 14) h
  simp (disch := omega) only [map_add, map_sub, two_nsmul, hs, hz, coeff_X_pow_self] at hc
  simp only [F, coeff_mk, Nat.reduceSub, add_zero, sub_zero, zero_add] at hc
  omega

end MetaMathlibExt
