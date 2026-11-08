/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeGapLiminf

example : primeGap 0 = 1 := by
  simp [primeGap, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

example : 2 ≤ MathlibExt.NumberTheory.primeGapLiminf :=
  MathlibExt.NumberTheory.two_le_primeGapLiminf

example : primeGap 1 = 2 := by
  simp [primeGap, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

example : primeGap 3 = 4 := by
  simp [primeGap, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]

example : MetaMathlibExt.AreConsecutivePrimes 3 5 := by
  simpa [Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five] using
    MathlibExt.NumberTheory.consecutive_nth_prime 1

example : ¬ MetaMathlibExt.AreConsecutivePrimes 3 7 := by
  rintro ⟨_, _, _, h⟩
  have := h 5 (by decide)
  omega

example (B : ℕ) : MathlibExt.NumberTheory.primeGapLiminf ≤ (B : WithTop ℕ) ↔
    Set.Infinite {n : ℕ | primeGap n ≤ B} :=
  MathlibExt.NumberTheory.primeGapLiminf_le_iff_infinite B

example (h : ∃ B : ℕ, 0 < B ∧ Set.Infinite {p : ℕ | Nat.Prime p ∧
    ∃ q : ℕ, Nat.Prime q ∧ p < q ∧ q - p ≤ B}) :
    MathlibExt.NumberTheory.primeGapLiminf ≠ ⊤ :=
  MathlibExt.NumberTheory.primeGapLiminf_ne_top_iff_bounded_pairs.mpr h

example : MathlibExt.NumberTheory.primeGapLiminf = 2 ↔
    Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} :=
  MathlibExt.NumberTheory.primeGapLiminf_eq_two_iff
