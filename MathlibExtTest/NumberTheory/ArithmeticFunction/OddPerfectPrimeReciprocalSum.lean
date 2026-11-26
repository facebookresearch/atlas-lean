/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted MetaMathlibExt

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

-- For least prime factor 3, the bound is 2 + 9 / 36 = 9 / 4.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h3 : n.minFac = 3) :
    abundancySup n ≤ 9 / 4 := by
  have h := oddPerfect_abundancySup_le n hodd hperf
  rw [h3] at h
  norm_num at h
  exact h

-- Every odd perfect number satisfies the uniform bound 9 / 4.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) : abundancySup n ≤ 9 / 4 := by
  have h := oddPerfect_abundancySup_le n hodd hperf
  have hn1 : n ≠ 1 := fun h1 => by simp [h1, Nat.Perfect] at hperf
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hpdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hp2 : n.minFac ≠ 2 := fun h2 => hodd.not_two_dvd_nat (h2 ▸ hpdvd)
  have hpge : 3 ≤ n.minFac := by
    have h2 := hp.two_le
    omega
  have h3 : (3 : ℚ) ≤ n.minFac := by exact_mod_cast hpge
  have hpos : (0 : ℚ) < n.minFac := by exact_mod_cast Nat.minFac_pos n
  have hsq : (9 : ℚ) ≤ (n.minFac : ℚ) ^ 2 := by nlinarith [h3, hpos]
  have hle : (2 : ℚ) + 9 / (4 * (n.minFac : ℚ) ^ 2) ≤ 9 / 4 := by
    have hx0 : (n.minFac : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hpos)
    have hxpos : (0 : ℚ) < (n.minFac : ℚ) ^ 2 := pow_pos hpos 2
    field_simp
    linarith
  calc abundancySup n ≤ 2 + 9 / (4 * (n.minFac : ℚ) ^ 2) := h
    _ ≤ 9 / 4 := hle

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum
