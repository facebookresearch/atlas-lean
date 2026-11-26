/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.TwoPowBinomialForm
import MathlibExt.NumberTheory.Digits.BinomialFormTwoPowBase
import Mathlib.Tactic.NormNum

/-! # Tests for the sufficient condition for binomial forms of powers of two -/

open MetaMathlibExt

-- x = 4, k = 3 and r = 2: since 4 * C(3, 2) = 12 < 15, the number 2 ^ 14 has a binomial form in
-- base 15, although r + k > x.
example : HasBinomialForm (2 ^ 4 - 1) (2 ^ 14) :=
  hasBinomialForm_two_pow 14 4 3 2 (by decide) (by decide) (by decide)

-- The digits behind it: 2 ^ 14 = (4, 12, 12, 4) in base 15, that is 4 * (1, 3, 3, 1).
example : Nat.digits 15 (2 ^ 14) = [4, 12, 12, 4] := by norm_num

-- A tight case: x = 3, k = 4 and r = 0, where the middle coefficient C(4, 2) = 6 is one less than
-- the base 7, and 2 ^ 12 = (1, 4, 6, 4, 1) in base 7.
example : HasBinomialForm 7 (2 ^ 12) :=
  hasBinomialForm_two_pow 12 3 4 0 (by decide) (by decide) (by decide)

-- With k = 1 and r = 0, every 2 ^ x with x ≥ 2 is written (1, 1) in base 2 ^ x - 1.
example (x : ℕ) (hx : 2 ≤ x) : HasBinomialForm (2 ^ x - 1) (2 ^ x) := by
  have h4 : 2 ^ 2 ≤ 2 ^ x := Nat.pow_le_pow_right (by decide) hx
  refine hasBinomialForm_two_pow x x 1 0 le_rfl (by ring) ?_
  norm_num
  omega

-- Together with Lemma 2, the scale of the binomial form found for 2 ^ 14 is a power of two.
example : ∃ α k : ℕ, (∃ i, α = 2 ^ i) ∧
    Nat.digits 15 (2 ^ 14) = (List.range (k + 1)).map fun i => α * k.choose i := by
  obtain ⟨α, k, hα, hk, hd⟩ := hasBinomialForm_two_pow 14 4 3 2 (by decide) (by decide) (by decide)
  exact ⟨α, k, (binomialForm_two_pow_base 14 15 α k (by decide) hα hk hd).2, hd⟩
