/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.SmallBaseBinomialForm
import MathlibExt.NumberTheory.Digits.BinomialFormTwoPowBase
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum

/-! # Tests for small bases of binomial forms of powers of two -/

open MetaMathlibExt

-- The smallest admissible exponent gives the two digits of 4 in base 3.
example : ∃ y b : ℕ, y ≤ ⌈Real.sqrt (2 * 2)⌉₊ + 1 ∧ 2 ≤ b ∧ b ≤ 2 ^ y - 1 ∧
    HasBinomialForm b (2 ^ 2) :=
  exists_small_base_binomialForm_two_pow 2 (by decide)

example : HasBinomialForm 3 (2 ^ 2) :=
  ⟨1, 1, by decide, by decide, by decide⟩

-- For n = 17, x = 6, k = 2 and r = 5. The paper's second branch gives
-- y = 7 and r' = 3, hence the digits [8, 16, 8] in base 127.
private theorem digits_seventeen :
    Nat.digits 127 (2 ^ 17) = (List.range (2 + 1)).map fun i => 8 * Nat.choose 2 i := by
  simpa only [show (2 : ℕ) ^ 17 = 8 * (1 + 127) ^ 2 by decide] using
    digits_mul_one_add_pow 8 2 127 (by decide) (by decide)

example : Nat.digits 127 (2 ^ 17) = [8, 16, 8] :=
  digits_seventeen.trans (by decide)

example : ∃ y b : ℕ, y ≤ ⌈Real.sqrt (2 * 17)⌉₊ + 1 ∧ 2 ≤ b ∧ b ≤ 2 ^ y - 1 ∧
    HasBinomialForm b (2 ^ 17) := by
  have h : (5 : ℝ) < Real.sqrt (2 * 17) := by
    apply (Real.lt_sqrt (by norm_num)).2
    norm_num
  have hlo : 5 < ⌈Real.sqrt (2 * 17)⌉₊ := Nat.lt_ceil.mpr h
  have hhi : ⌈Real.sqrt (2 * 17)⌉₊ ≤ 6 := by
    apply Nat.ceil_le.mpr (Real.sqrt_le_iff.mpr ?_)
    norm_num
  have hx : ⌈Real.sqrt (2 * 17)⌉₊ = 6 := by omega
  rw [hx]
  exact ⟨7, 127, by decide, by decide, by decide, 8, 2, by decide, by decide, digits_seventeen⟩

example : (∃ x ≤ 17, 127 = 2 ^ x - 1) ∧ ∃ i : ℕ, 8 = 2 ^ i :=
  binomialForm_two_pow_base 17 127 8 2 (by decide) (by decide) (by decide) digits_seventeen
