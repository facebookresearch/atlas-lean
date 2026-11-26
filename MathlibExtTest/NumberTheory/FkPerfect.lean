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

-- `2 = 2 ^ 1` is `[2,1]`-deficient-perfect, so the theorem recovers `ℓ = 1`.
example : (1 : ℕ) = 1 ∧ (1 = 2 ∨ (2 = 2 ∧ 1 = 1)) :=
  isKLDeficientPerfect_prime_pow_two_imp 2 1 1 Nat.prime_two
    (by simpa using isKLDeficientPerfect_two 2)

-- Every `[2,ℓ]`-deficient-perfect prime power has `ℓ = 1`.
example (p a l : ℕ) (hp : p.Prime) (h : IsKLDeficientPerfect 2 l (p ^ a)) : l = 1 :=
  (isKLDeficientPerfect_prime_pow_two_imp p a l hp h).1

-- `2 = 2 ^ 1` is the only `[2,ℓ]`-deficient-perfect prime power.
example : IsKLDeficientPerfect 2 1 (2 ^ 1) :=
  (isKLDeficientPerfect_prime_pow_two_iff 2 1 1 Nat.prime_two).mpr ⟨rfl, rfl, rfl⟩

-- The exception `a = 2` of the printed statement does not occur: no prime square is
-- `[2,ℓ]`-deficient-perfect.
example (p l : ℕ) (hp : p.Prime) : ¬ IsKLDeficientPerfect 2 l (p ^ 2) := fun h =>
  absurd ((isKLDeficientPerfect_prime_pow_two_iff p 2 l hp).mp h).2.1 (by decide)

end MathlibExtTest.NumberTheory.FkPerfect
