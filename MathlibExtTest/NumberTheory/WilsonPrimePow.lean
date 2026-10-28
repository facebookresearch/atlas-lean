/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WilsonPrimePow

/-!
# Tests for Wilson's theorem modulo prime powers
-/

@[expose] public section

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### Square roots of `1` modulo `2 ^ s` -/

-- `3 ^ 2 ≡ 1 (mod 8)` and `3 = 2 ^ 2 - 1`.
example : (3 : ℤ) ^ 2 ≡ 1 [ZMOD 2 ^ 3] :=
  (Int.sq_modEq_one_two_pow_iff (by norm_num) 3).mpr (Or.inr (Or.inr (Or.inl (by decide))))

-- `5 ^ 2 ≢ 1 (mod 16)`: `5` is none of `1, -1, 7, 9` modulo `16`.
example : ¬ (5 : ℤ) ^ 2 ≡ 1 [ZMOD 2 ^ 4] := by
  rw [Int.sq_modEq_one_two_pow_iff (by norm_num)]
  decide

-- The hypothesis `2 ≤ s` is needed: modulo `2` the right-hand side holds for `x = 0`.
example : ¬ ((0 : ℤ) ^ 2 ≡ 1 [ZMOD 2 ^ 1]) ∧ (0 : ℤ) ≡ 2 ^ (1 - 1) + 1 [ZMOD 2 ^ 1] := by
  decide

/-! ### Products of units -/

example : ∏ g : (ZMod 5)ˣ, g = ∏ g ∈ Finset.univ.filter (fun g : (ZMod 5)ˣ => g ^ 2 = 1), g :=
  prod_univ_eq_prod_filter_sq_eq_one _

example : orderOf (-1 : (ZMod (3 ^ (1 + 1)))ˣ) = 2 :=
  ZMod.orderOf_neg_one_units_prime_pow 3 1 (by decide)

-- Gauss's generalisation of Wilson: modulo `9` and `25` the units multiply to `-1`.
example : ∏ u : (ZMod (3 ^ (1 + 1)))ˣ, (u : ZMod (3 ^ (1 + 1))) = -1 :=
  ZMod.prod_units_prime_pow_eq_neg_one 3 1 (by decide)

example : ∏ u : (ZMod (5 ^ (1 + 1)))ˣ, (u : ZMod (5 ^ (1 + 1))) = -1 :=
  ZMod.prod_units_prime_pow_eq_neg_one 5 1 (by decide)

-- Modulo `8 = 2 ^ (0 + 3)` the units multiply to `1`, ...
example : ∏ u : (ZMod (2 ^ (0 + 3)))ˣ, u = 1 := ZMod.prod_units_two_pow_eq_one 0

-- ... while modulo `4` they multiply to `-1`, so `s ≥ 3` is needed.
example : ∏ u : (ZMod 4)ˣ, (u : ZMod 4) = -1 := by decide

-- Modulo `8` the unit `3` squares to `1` but is not `±1`, so `p ≠ 2` is needed in
-- `units_eq_one_or_eq_neg_one_of_sq_eq_one`.
example : ∃ u : (ZMod 8)ˣ, u ^ 2 = 1 ∧ u ≠ 1 ∧ u ≠ -1 := by decide

example (u : (ZMod (5 ^ (0 + 1)))ˣ) (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 :=
  ZMod.units_eq_one_or_eq_neg_one_of_sq_eq_one 5 0 (by decide) u hu

-- The integers prime to `3` in `{1, 2, 3}` multiply to `2 = -1 (mod 3)`.
example : ∏ j ∈ (Finset.range (3 ^ 1)).filter (fun j => ¬ 3 ∣ 1 + j),
    ((1 + j : ℕ) : ZMod (3 ^ 1)) = ∏ u : (ZMod (3 ^ 1))ˣ, (u : ZMod (3 ^ 1)) :=
  ZMod.prod_range_filter_not_dvd_add_eq_prod_units 3 1 1 (by decide)

example : ∏ j ∈ (Finset.range (3 ^ 1)).filter (fun j => ¬ 3 ∣ 1 + j),
    ((1 + j : ℕ) : ZMod (3 ^ 1)) = -1 := by
  decide

/-! ### `(p - k)! (k - 1)! ≡ (-1) ^ k (mod p)` -/

-- `p = 5`, `k = 2`: `3! · 1! = 6 ≡ 1`.
example : (((5 - 2).factorial * (2 - 1).factorial : ℕ) : ZMod 5) = (-1) ^ 2 :=
  ZMod.factorial_sub_mul_factorial_pred 5 (by norm_num) (by norm_num)

example : (((5 - 3).factorial * (3 - 1).factorial : ℕ) : ZMod 5) = -1 := by
  rw [ZMod.factorial_sub_mul_factorial_pred 5 (by norm_num) (by norm_num)]
  norm_num

-- `k = p - 1` recovers Wilson's theorem `(p - 1)! ≡ -1`... up to the factor `1! = 1`.
example : (((7 - 6).factorial * (6 - 1).factorial : ℕ) : ZMod 7) = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [ZMod.factorial_sub_mul_factorial_pred 7 (by norm_num) (by norm_num)]
  norm_num
