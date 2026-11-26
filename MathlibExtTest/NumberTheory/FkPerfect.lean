/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfect

/-! # Tests for `MathlibExt.NumberTheory.FkPerfect` -/

namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

-- `8 = 2 ^ 3` is `[1, 1]`-deficient-perfect with divisor `1`.
example : KLDeficientPerfectWith 1 1 (2 ^ 3) 1 :=
  (klDeficientPerfectWith_one_prime_pow_iff 2 3 1 1 Nat.prime_two).mpr
    ⟨rfl, rfl, rfl, by decide⟩

-- Every power of two from `2 ^ 1` on is `[1, 1]`-deficient-perfect with divisor `1`.
example (a : ℕ) (ha : 1 ≤ a) : IsKLDeficientPerfect 1 1 (2 ^ a) :=
  ⟨1, (klDeficientPerfectWith_one_prime_pow_iff 2 a 1 1 Nat.prime_two).mpr
    ⟨rfl, rfl, rfl, ha⟩⟩

-- No power of `3` is `[1, ℓ]`-deficient-perfect with any divisor.
example (a l d : ℕ) : ¬ KLDeficientPerfectWith 1 l (3 ^ a) d := by
  intro h
  have h2 := (klDeficientPerfectWith_one_prime_pow_iff 3 a l d (by decide)).mp h
  exact (by decide : (3 : ℕ) ≠ 2) h2.1

-- At exponent zero, `2 ^ 0 = 1` has no proper divisor, so the predicate is false.
example (l d : ℕ) : ¬ KLDeficientPerfectWith 1 l (2 ^ 0) d := by
  intro h
  have h2 := (klDeficientPerfectWith_one_prime_pow_iff 2 0 l d Nat.prime_two).mp h
  exact absurd h2.2.2.2 (by decide)

-- `18 = 2 ^ 1 * 3 ^ 2` is not near `F`-perfect.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect 18 := by
  simpa using MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime_pow
    3 1 2 (by decide) (by decide)

-- `2500 = 2 ^ 2 * 5 ^ 4` is not near `F`-perfect.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect 2500 := by
  simpa using MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime_pow
    5 2 4 (by decide) (by decide)

-- `8 = 2 ^ 3 * 11 ^ 0` is not near `F`-perfect.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect 8 := by
  simpa using MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime_pow
    11 3 0 (by decide) (by decide)

-- `3 * 5` is not near `F₂`-perfect: both exponents are odd.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFkPerfect 2 (3 * 5) := by
  have h := MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFkPerfect_pow_mul_pow
    2 3 5 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    le_rfl le_rfl (Or.inr ⟨by decide, by decide⟩)
  simpa using h

-- `3 * 5 ^ 2` is not near `F₂`-perfect: the exponent sum is odd.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFkPerfect 2 (3 * 5 ^ 2) :=
  MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFkPerfect_pow_mul_pow
    2 3 5 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    le_rfl (by decide) (Or.inl (by decide))

-- With `p₁ = p₂` the conclusion fails: `9 = 3 ^ 1 * 3 ^ 1` is near `F_3`-perfect with `d = 1`.
example : MathlibExt.NumberTheory.FkPerfectWanted.IsNearFkPerfect 3 (3 ^ 1 * 3 ^ 1) :=
  ⟨1, by decide, by decide, by decide⟩

end MathlibExtTest.NumberTheory.FkPerfect
