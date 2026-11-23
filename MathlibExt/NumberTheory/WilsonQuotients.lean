/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Factorial
import Mathlib.NumberTheory.Wilson

/-!
# A generalized Wilson criterion for primality

Splitting off the last `k` factors of `(n - 1)!` gives `(-1)^k * k!` for their product
modulo `n`. This reduces Morozov's criterion to Wilson's theorem.
-/

public section

namespace MathlibExt.NumberTheory.WilsonQuotientsWanted

/-- **A generalized Wilson criterion for primality.** Let $n \ge 1$ and $k < n$ be natural
numbers. Then $(-1)^k \, k! \, (n - k - 1)! \equiv -1 \pmod{n}$ if and only if $n = 1$ or $n$
is prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Corollary 1. -/
theorem neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff
    (n k : ℕ) (hn : 1 ≤ n) (hk : k < n) :
    ((-1 : ℤ) ^ k * (Nat.factorial k * Nat.factorial (n - k - 1) : ℤ) ≡
        -1 [ZMOD (n : ℤ)]) ↔
      n = 1 ∨ n.Prime := by
  rcases eq_or_lt_of_le hn with rfl | hn
  · exact iff_of_true Int.modEq_one (Or.inl rfl)
  rw [or_iff_right hn.ne', Nat.prime_iff_fac_equiv_neg_one hn.ne', ← ZMod.intCast_eq_intCast_iff]
  rw [← Nat.factorial_mul_descFactorial (show k ≤ n - 1 by omega), Nat.cast_mul,
    ZMod.cast_descFactorial hk.le, tsub_right_comm (b := 1) (c := k)]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    mul_comm, mul_left_comm]

end MathlibExt.NumberTheory.WilsonQuotientsWanted
