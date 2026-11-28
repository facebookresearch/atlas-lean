/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Enumerative.RepeatingDecimalRatio
import Mathlib.Tactic.NormNum

/-!
# Tests for the repeating-decimal ratio count
-/

open MetaMathlibExt

-- For one repeating digit the two solutions have numerators 10 and 34.
example : {x : ℕ | 10 ≤ x ∧ x < 100 ∧ ∃ k : ℕ, x ≤ k ∧ k < 2 * x ∧
    (k : ℚ) / x = 1 + ((x : ℚ) - 10) / 9} = {10, 18} := by
  let S := {x : ℕ | 10 ≤ x ∧ x < 100 ∧ ∃ k : ℕ, x ≤ k ∧ k < 2 * x ∧
    (k : ℚ) / x = 1 + ((x : ℚ) - 10) / 9}
  have hcard : S.ncard = 2 := by
    have h := ncard_repeating_decimal_ratio_eq_two_pow_omega 1 (by decide)
    norm_num at h
    rw [show 9 = 3 ^ 2 by decide,
      ArithmeticFunction.cardDistinctFactors_apply_prime_pow Nat.prime_three (by decide)] at h
    exact h
  apply Eq.symm
  refine Set.eq_of_subset_of_ncard_le (t := S) ?_ ?_ (Set.finite_of_ncard_pos (by omega))
  · rintro x (rfl | hx)
    · exact ⟨by decide, by decide, 10, by decide, by decide, by norm_num⟩
    · obtain rfl : x = 18 := hx
      exact ⟨by decide, by decide, 34, by decide, by decide, by norm_num⟩
  · rw [hcard, Set.ncard_pair (by decide)]

-- The repeated prime in 99 = 3² * 11 contributes only one factor of two.
example : {x : ℕ | 100 ≤ x ∧ x < 1000 ∧ ∃ k : ℕ, x ≤ k ∧ k < 2 * x ∧
    (k : ℚ) / x = 1 + ((x : ℚ) - 100) / 99}.ncard = 4 := by
  have h := ncard_repeating_decimal_ratio_eq_two_pow_omega 2 (by decide)
  norm_num at h
  rw [show 99 = 3 ^ 2 * 11 by decide,
    ArithmeticFunction.cardDistinctFactors_mul (by decide : Nat.Coprime (3 ^ 2) 11),
    ArithmeticFunction.cardDistinctFactors_apply_prime_pow Nat.prime_three (by decide),
    ArithmeticFunction.cardDistinctFactors_apply_prime (by decide : Nat.Prime 11)] at h
  exact h
