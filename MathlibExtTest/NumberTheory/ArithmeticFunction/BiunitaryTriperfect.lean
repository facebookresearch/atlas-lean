/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfect

/-! # Tests for `MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfect` -/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.BiunitaryTriperfect

open MetaMathlibExt

-- At `p = 2`, `m = 1`, `e = 3`, the first bound reads `5 / 4 ≤ σ**(8) / 8`.
example : (5 / 4 : ℚ) ≤ (sigmaBiunitary (2 ^ 3) : ℚ) / ((2 : ℕ) : ℚ) ^ 3 := by
  have hLHS : (sigmaBiunitary (2 ^ (2 * 1)) : ℚ) / ((2 : ℕ) : ℚ) ^ (2 * 1) = 5 / 4 := by
    have hexp : (2 : ℕ) ^ (2 * 1) = 4 := by decide
    have hexp2 : 2 * 1 = 2 := by decide
    rw [hexp, hexp2, sigmaBiunitary_four]
    norm_num
  rw [← hLHS]
  exact (sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le 2 1 3
    (by decide) (by decide) (by decide)).1

-- At `p = 2`, `m = 1`, `e = 3`, the second bound reads `3 / 2 ≤ σ**(8) / 8`.
example : (3 / 2 : ℚ) ≤ (sigmaBiunitary (2 ^ 3) : ℚ) / ((2 : ℕ) : ℚ) ^ 3 := by
  have hsum : ∑ i ∈ Finset.range (1 + 1), 1 / ((2 : ℕ) : ℚ) ^ i = 3 / 2 := by
    norm_num [Finset.sum_range_succ]
  rw [← hsum]
  exact (sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le 2 1 3
    (by decide) (by decide) (by decide)).2 (by decide)

-- At `p = 3`, `m = 2`, `e = 3`, the second bound is nearly tight: `13 / 9 ≤ 40 / 27`.
example : (13 / 9 : ℚ) ≤ (sigmaBiunitary (3 ^ 3) : ℚ) / ((3 : ℕ) : ℚ) ^ 3 := by
  have hsum : ∑ i ∈ Finset.range (2 + 1), 1 / ((3 : ℕ) : ℚ) ^ i = 13 / 9 := by
    norm_num [Finset.sum_range_succ]
  rw [← hsum]
  exact (sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le 3 2 3
    (by decide) (by decide) (by decide)).2 (by decide)

-- Successive exponents give a monotone chain at `p = 2`.
example (m : ℕ) (hm : 0 < m) :
    (sigmaBiunitary (2 ^ (2 * m)) : ℚ) / ((2 : ℕ) : ℚ) ^ (2 * m) ≤
      (sigmaBiunitary (2 ^ (2 * m + 1)) : ℚ) / ((2 : ℕ) : ℚ) ^ (2 * m + 1) :=
  (sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le 2 m (2 * m + 1)
    (by decide) hm (by omega)).1

-- A biunitary triperfect number with `3`-exponent at least `3` is divisible by `16`.
example (N : ℕ) (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N)
    (hf : 3 ≤ N.factorization 3) : 16 ∣ N := by
  have h4 := four_le_factorization_two_of_biunitaryTriperfect N hN hσ hf
  have h24 : (2 : ℕ) ^ 4 ∣ N :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hN.ne').mpr h4
  have h216 : (2 : ℕ) ^ 4 = 16 := rfl
  rw [h216] at h24
  exact h24

-- The same conclusion from the divisibility hypothesis `27 ∣ N`.
example (N : ℕ) (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N) (h27 : 27 ∣ N) :
    16 ∣ N := by
  have hf : 3 ≤ N.factorization 3 := by
    have h33 : (3 : ℕ) ^ 3 ∣ N := by
      have h273 : (27 : ℕ) = 3 ^ 3 := rfl
      rw [h273] at h27
      exact h27
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hN.ne').mp h33
  have h4 := four_le_factorization_two_of_biunitaryTriperfect N hN hσ hf
  have h24 : (2 : ℕ) ^ 4 ∣ N :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hN.ne').mpr h4
  have h216 : (2 : ℕ) ^ 4 = 16 := rfl
  rw [h216] at h24
  exact h24

end MathlibExtTest.NumberTheory.ArithmeticFunction.BiunitaryTriperfect
