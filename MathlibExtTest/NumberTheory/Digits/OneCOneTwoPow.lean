/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.OneCOneTwoPow

/-! # Tests for powers of two with outer digits one -/

open MetaMathlibExt

-- The factorization in the paper's base-151 example gives a non-binomial palindrome.
example : ∃ c, c ≠ 2 ∧ Nat.digits 151 (2 ^ 15) = [1, c, 1] :=
  (one_c_one_two_pow_iff 15 151 (by decide)).2 ⟨⟨217, by decide⟩, by decide⟩

-- An even exponent also works when the base differs from the exceptional one.
example : ∃ c, c ≠ 2 ∧ Nat.digits 399 (2 ^ 18) = [1, c, 1] :=
  (one_c_one_two_pow_iff 18 399 (by decide)).2 ⟨⟨657, by decide⟩, by decide⟩

-- In base three the factorization 15 = 5 * 3 fits the bounds, but 16 has middle digit two.
example : ¬ ∃ c, c ≠ 2 ∧ Nat.digits 3 (2 ^ 4) = [1, c, 1] := by
  intro h
  exact ((one_c_one_two_pow_iff 4 3 (by decide)).1 h).2 (by decide)
