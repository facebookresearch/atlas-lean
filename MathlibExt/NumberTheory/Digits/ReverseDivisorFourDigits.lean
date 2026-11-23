/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisor

/-!
# Reverse divisors have at least four digits

By the classification of reverse divisors with at most seven digits, a reverse divisor with at
most three decimal digits would be `0`, `99` or `198`. None of these is a reverse divisor: `0` is
not positive, `99` has only two digits, and the reversal `891` of `198` is not a multiple of
`198`.
-/

public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- **Reverse divisors have at least four digits.** Every reverse divisor has at least four
decimal digits.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem four_le_length_digits (n : ℕ)
    (h : IsReverseDivisor n) :
    4 ≤ (Nat.digits 10 n).length := by
  by_contra hlt
  have hbasic := eq_basic_of_length_le_seven n h (by omega)
  obtain h0 | h3 : (Nat.digits 10 n).length - 2 = 0 ∨ (Nat.digits 10 n).length = 3 := by omega
  · -- With at most two digits both formulas give `0`, but a reverse divisor is positive.
    simp only [h0, pow_zero, Nat.sub_self, Nat.mul_zero, or_self] at hbasic
    exact h.1.ne' hbasic
  · -- With three digits the formulas give `99` and `198`.
    rw [h3] at hbasic
    obtain rfl | rfl : n = 99 ∨ n = 198 := by simpa using hbasic
    · -- `99` has two digits, not three.
      simp at h3
    · -- The reversal `891` of `198` lies strictly between `4 * 198` and `5 * 198`.
      obtain ⟨-, k, -, hk⟩ := h
      rw [show Nat.reverseDigits 10 198 = 891 by decide] at hk
      omega

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
