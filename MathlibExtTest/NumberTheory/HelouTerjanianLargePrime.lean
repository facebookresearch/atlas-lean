/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HelouTerjanianLargePrime

/-!
# Tests for the Helou–Terjanian congruence at primes at least five
-/

open MetaMathlibExt

-- The smallest admissible case attains the bound: `C(10, 5) = 252` is `2` modulo `5 ^ 3` only.
example : (10 : ℕ).choose 5 ≡ 2 [MOD 125] ∧ ¬ (10 : ℕ).choose 5 ≡ 2 [MOD 625] := by
  refine ⟨?_, by decide⟩
  convert choose_mul_prime_modEq_of_five_le 5 2 1 Nat.prime_five le_rfl one_pos one_lt_two
    using 1 <;> decide +kernel

-- For complementary lower indices, each side of the maximum in turn supplies a power of five,
-- and the exponent four is attained.
example : (30 : ℕ).choose 5 ≡ 6 [MOD 625] ∧ ¬ (30 : ℕ).choose 5 ≡ 6 [MOD 3125] := by
  refine ⟨?_, by decide +kernel⟩
  convert choose_mul_prime_modEq_of_five_le 5 6 1 Nat.prime_five le_rfl one_pos (by decide)
    using 1 <;> decide +kernel

example : (30 : ℕ).choose 25 ≡ 6 [MOD 625] := by
  convert choose_mul_prime_modEq_of_five_le 5 6 5 Nat.prime_five le_rfl (by decide)
    (by decide) using 1 <;> decide +kernel

-- The valuation of the binomial coefficient adds to the exponent: `C(5, 1) = 5`.
example : (25 : ℕ).choose 5 ≡ 5 [MOD 625] := by
  convert choose_mul_prime_modEq_of_five_le 5 5 1 Nat.prime_five le_rfl one_pos (by decide)
    using 1 <;> decide +kernel

-- A larger prime.
example : (21 : ℕ).choose 14 ≡ 3 [MOD 7 ^ 3] := by
  convert choose_mul_prime_modEq_of_five_le 7 3 2 Nat.prime_seven (by decide) two_pos
    (by decide) using 1 <;> decide +kernel

-- Wolstenholme's congruence `C(2p, p) ≡ 2 (mod p ^ 3)` is the case `n = 2`, `m = 1`.
example (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : (2 * p).choose p ≡ 2 [MOD p ^ 3] := by
  have h := choose_mul_prime_modEq_of_five_le p 2 1 hp hp5 one_pos one_lt_two
  have h2 : multiplicity p 2 = 0 := multiplicity_eq_zero_of_not_dvd fun hd => by
    have := Nat.le_of_dvd two_pos hd
    omega
  simpa [Nat.padicValNat_def, multiplicity_one_right, h2] using h
