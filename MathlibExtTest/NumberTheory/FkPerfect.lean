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

-- A concrete instance with a positive exponent.
example : ¬ IsDeficientFkPerfect 2 (3 ^ 5 * 5) :=
  not_isDeficientFkPerfect_prime_pow_mul (k := 2) (p₁ := 3) (p₂ := 5) (a := 5)
    (hk := by decide) (hp₁ := by decide) (hp₂ := by decide)
    (ho₁ := ⟨1, rfl⟩) (ho₂ := ⟨2, rfl⟩) (hne := by decide)

-- The zero exponent is included: `5 ^ 0 * 7` is the prime `7`.
example : ¬ IsDeficientFkPerfect 3 (5 ^ 0 * 7) :=
  not_isDeficientFkPerfect_prime_pow_mul (k := 3) (p₁ := 5) (p₂ := 7) (a := 0)
    (hk := by decide) (hp₁ := by decide) (hp₂ := by decide)
    (ho₁ := ⟨2, rfl⟩) (ho₂ := ⟨3, rfl⟩) (hne := by decide)

-- Specialized to `3 ^ a * 5`, the statement holds for every exponent.
example (a : ℕ) : ¬ IsDeficientFkPerfect 2 (3 ^ a * 5) :=
  not_isDeficientFkPerfect_prime_pow_mul (k := 2) (p₁ := 3) (p₂ := 5) (a := a)
    (hk := by decide) (hp₁ := by decide) (hp₂ := by decide)
    (ho₁ := ⟨1, rfl⟩) (ho₂ := ⟨2, rfl⟩) (hne := by decide)

end MathlibExtTest.NumberTheory.FkPerfect
