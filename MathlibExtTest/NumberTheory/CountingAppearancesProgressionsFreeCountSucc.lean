/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Prime.Nth
import MathlibExt.NumberTheory.CountingAppearancesProgressionsFreeCountSucc

/-! # Tests for the first-prime free-count recurrence -/

namespace MathlibExtTest.NumberTheory.CountingAppearancesProgressionsFreeCountSucc

open MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

-- The first step multiplies the one-prime free count by 3 − 1.
example : freeCount (firstPrimes 2) ![3, 5] = 2 := by
  have h : firstPrimes 1 = ![2] := by
    funext i
    rw [Fin.eq_zero i]
    simp [firstPrimes, Nat.nth_prime_zero_eq_two]
  rw [freeCount_firstPrimes_succ 1 (by decide), Nat.nth_prime_one_eq_three, h]
  decide

-- At the next step the residue 12 represents 2 modulo 5.
example : freeCount (firstPrimes 3) ![0, 2, 12] = 8 := by
  have h : firstPrimes 2 = ![2, 3] := by
    funext i
    fin_cases i <;> simp [firstPrimes, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  rw [freeCount_firstPrimes_succ 2 (by decide), Nat.nth_prime_two_eq_five, h]
  decide

end MathlibExtTest.NumberTheory.CountingAppearancesProgressionsFreeCountSucc
