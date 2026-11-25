/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.PalindromicTwoPowBinomialForm

/-! # Tests for binomial forms of palindromic powers of two -/

open MetaMathlibExt

-- Single digit: the coefficient bound uses the exact digit count.
example : 0 * (2 - 1) < (1 : ℕ) ∧ Nat.digits 3 (2 ^ 1) = [2] := by
  have h := palindrome_two_pow_base_two_pow_sub_one 2 1 0 (by decide) (by decide)
    (by decide) (by decide)
  exact ⟨h.1, h.2 1 rfl (Or.inl (by decide))⟩

-- The first bound is tight at `r + k = x`.
example : 2 * (2 - 1) < (4 : ℕ) ∧ Nat.digits 3 (2 ^ 4) = [1, 2, 1] := by
  have h := palindrome_two_pow_base_two_pow_sub_one 2 4 2 (by decide) (by decide)
    (by decide) (by decide)
  exact ⟨h.1, h.2 0 rfl (Or.inl (by decide))⟩

-- Here `r + k = x + 1`, so only the second bound applies (in the first row it covers).
example : 3 * (3 - 1) < (10 : ℕ) ∧ Nat.digits 7 (2 ^ 10) = [2, 6, 6, 2] := by
  have h := palindrome_two_pow_base_two_pow_sub_one 3 10 3 (by decide) (by decide)
    (by decide) (by decide)
  exact ⟨h.1, h.2 1 rfl (Or.inr ⟨by decide, by decide, by decide⟩)⟩

-- The next row uses the second bound with `r = 0`.
example : 4 * (3 - 1) < (12 : ℕ) ∧ Nat.digits 7 (2 ^ 12) = [1, 4, 6, 4, 1] := by
  have h := palindrome_two_pow_base_two_pow_sub_one 3 12 4 (by decide) (by decide)
    (by decide) (by decide)
  exact ⟨h.1, h.2 0 rfl (Or.inr ⟨by decide, by decide, by decide⟩)⟩
