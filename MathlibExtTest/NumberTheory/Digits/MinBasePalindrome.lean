/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.MinBasePalindrome
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.Digits.MinBasePalindrome` -/

namespace MathlibExtTest.MinBasePalindrome

open MetaMathlibExt

-- Test section: concrete palindromes with an even number of digits, so the hypotheses can hold.

-- Base 10: `123321 = 11 * 11211`.
example : 11 ∣ 123321 :=
  succ_dvd_of_palindrome_even_length 123321 10 (by norm_num) (by decide) (by decide)

-- Base 2: `51 = (1, 1, 0, 0, 1, 1)_2 = 3 * 17`.
example : 3 ∣ 51 :=
  succ_dvd_of_palindrome_even_length 51 2 le_rfl (by decide) (by decide)

-- Powers of two: `2 ^ 3 = (2, 2)_3` and `2 ^ 6 = (4, 4)_15`.
example : 4 ∣ 2 ^ 3 :=
  succ_dvd_of_palindrome_even_length (2 ^ 3) 3 (by norm_num) (by decide) (by decide)

example : 16 ∣ 2 ^ 6 :=
  succ_dvd_of_palindrome_even_length (2 ^ 6) 15 (by norm_num) (by decide) (by decide)

-- Edge case: `0` has no digits, and the empty list is a palindrome of even length `0`.
example (b : ℕ) (hb : 2 ≤ b) : b + 1 ∣ 0 :=
  succ_dvd_of_palindrome_even_length 0 b hb (by simp [List.Palindrome.nil]) (by simp)

-- Test section: general consequences.

-- In base `10` this is Mathlib's divisibility of even-length decimal palindromes by `11`.
example (n : ℕ) (hp : (Nat.digits 10 n).Palindrome) (he : Even (Nat.digits 10 n).length) :
    11 ∣ n :=
  succ_dvd_of_palindrome_even_length n 10 (by norm_num) hp he

-- The two-digit palindrome `(d, d)_b = d + b * d` for a digit `0 < d < b`.
example (b d : ℕ) (hb : 2 ≤ b) (hd : d ≠ 0) (hdb : d < b) : b + 1 ∣ d + b * d := by
  have hdig : Nat.digits b (d + b * d) = [d, d] := by
    rw [Nat.digits_add b (by omega) d d hdb (Or.inl hd), Nat.digits_of_lt b d hd hdb]
  exact succ_dvd_of_palindrome_even_length _ b hb (by rw [hdig]; exact .of_reverse_eq rfl)
    (by rw [hdig]; exact ⟨1, rfl⟩)

-- A prime whose base-`b` digits form an even-length palindrome is `b + 1`, such as
-- `11 = (1, 1)_10`.
example (N b : ℕ) (hb : 2 ≤ b) (hN : N.Prime) (hp : (Nat.digits b N).Palindrome)
    (he : Even (Nat.digits b N).length) : N = b + 1 :=
  ((hN.eq_one_or_self_of_dvd _ (succ_dvd_of_palindrome_even_length N b hb hp he)).resolve_left
    (by omega)).symm

-- The smallest allowed base: `3 = (1, 1)_2`.
example : ∃ x : ℕ, 2 = 3 ^ x - 1 :=
  base_eq_prime_pow_sub_one_of_palindrome 3 1 2 Nat.prime_three le_rfl (by decide) (by decide)

-- `3 ^ 3 = (3, 3)_8`, where the exponent in `8 + 1 = 3 ^ 2` is less than the input exponent.
example : ∃ x : ℕ, 8 = 3 ^ x - 1 :=
  base_eq_prime_pow_sub_one_of_palindrome 3 3 8 Nat.prime_three (by decide) (by decide) (by decide)

-- Powers of two: `2 ^ 3 = (2, 2)_3`, and `2 ^ 9 = 8 ^ 3 = (1, 3, 3, 1)_7` with four digits.
example : ∃ x : ℕ, 3 = 2 ^ x - 1 :=
  base_eq_two_pow_sub_one_of_palindrome 3 3 (by norm_num) (by decide) (by decide)

example : ∃ x : ℕ, 7 = 2 ^ x - 1 :=
  base_eq_two_pow_sub_one_of_palindrome 9 7 (by norm_num) (by decide) (by decide)

-- Since `2` is not one less than a power of two, no binary representation of a power of two is a
-- palindrome with an even number of digits.
example (n : ℕ) :
    ¬ ((Nat.digits 2 (2 ^ n)).Palindrome ∧ Even (Nat.digits 2 (2 ^ n)).length) := by
  rintro ⟨hp, he⟩
  obtain ⟨x, hx⟩ := base_eq_two_pow_sub_one_of_palindrome n 2 le_rfl hp he
  rcases x with _ | x
  · simp at hx
  · rw [pow_succ] at hx
    omega

-- Test section: neither hypothesis can be dropped.

-- `101 = (1, 0, 1)_10` is a palindrome with an odd number of digits, and `11 ∤ 101`.
example : (Nat.digits 10 101).Palindrome ∧ ¬ Even (Nat.digits 10 101).length ∧ ¬ 11 ∣ 101 := by
  decide

-- `12 = (1, 2)_10` has an even number of digits but is not a palindrome, and `11 ∤ 12`.
example : ¬ (Nat.digits 10 12).Palindrome ∧ Even (Nat.digits 10 12).length ∧ ¬ 11 ∣ 12 := by
  decide

-- Powers of two in base `5`: `2 ^ 2 = (4)_5` is a palindrome with an odd number of digits,
-- `2 ^ 3 = (1, 3)_5` has an even number of digits but is not a palindrome, and `5` is not one
-- less than a power of two.
example : (Nat.digits 5 (2 ^ 2)).Palindrome ∧ ¬ Even (Nat.digits 5 (2 ^ 2)).length ∧
    ¬ (Nat.digits 5 (2 ^ 3)).Palindrome ∧ Even (Nat.digits 5 (2 ^ 3)).length ∧
    ¬ ∃ x, 5 = 2 ^ x - 1 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨x, hx⟩
  rcases x with _ | _ | _ | x <;> simp [pow_succ] at hx
  omega

end MathlibExtTest.MinBasePalindrome
