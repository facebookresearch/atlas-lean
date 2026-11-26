/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerIsUnitarySZumkellerBounds

/-! # Tests for lower bounds for unitary s-Zumkeller numbers -/

namespace MathlibExtTest.NumberTheory.SZumkellerIsUnitarySZumkellerBounds

open MetaMathlibExt

/-- The least unitary divisor of `60` exceeding `1` is `3`. -/
private theorem least_unitaryDivisor_sixty :
    IsLeast {d | d ∈ Nat.unitaryDivisors 60 ∧ 1 < d} 3 := by
  have h60 : Nat.unitaryDivisors 60 = {1, 3, 4, 5, 12, 15, 20, 60} := by decide
  constructor
  · show 3 ∈ Nat.unitaryDivisors 60 ∧ 1 < 3
    rw [h60]
    decide
  · intro d hd
    simp only [Set.mem_ofPred_eq, h60, Finset.mem_insert, Finset.mem_singleton] at hd
    omega

-- At `n = 60` the first bound evaluates to `4400`.
example : (4400 : ℚ) ≤ ∑ d ∈ Nat.unitaryDivisors 60, (d : ℚ) ^ 2 := by
  have h := (isUnitarySZumkeller_bounds 60 3 isUnitarySZumkeller_sixty
    least_unitaryDivisor_sixty).1
  norm_num at h
  exact h

-- At `n = 60` the reciprocal-squares bound evaluates to `11 / 9`.
example : (11 / 9 : ℚ) ≤ ∑ d ∈ Nat.unitaryDivisors 60, 1 / (d : ℚ) ^ 2 := by
  have h := (isUnitarySZumkeller_bounds 60 3 isUnitarySZumkeller_sixty
    least_unitaryDivisor_sixty).2.1
  rw [show (2 : ℚ) / (((3 : ℕ) : ℚ)) ^ 2 + 1 = 11 / 9 by norm_num] at h
  exact h

-- At `n = 60` the prime-factor product bound applies directly.
example : (11 / 9 : ℚ) ≤ ∏ p ∈ (60 : ℕ).primeFactors,
    (1 + ((p : ℚ) ^ (60 : ℕ).factorization p) ^ 2) /
      ((p : ℚ) ^ (60 : ℕ).factorization p) ^ 2 := by
  have h := (isUnitarySZumkeller_bounds 60 3 isUnitarySZumkeller_sixty
    least_unitaryDivisor_sixty).2.2
  rw [show (2 : ℚ) / (((3 : ℕ) : ℚ)) ^ 2 + 1 = 11 / 9 by norm_num] at h
  exact h

end MathlibExtTest.NumberTheory.SZumkellerIsUnitarySZumkellerBounds
