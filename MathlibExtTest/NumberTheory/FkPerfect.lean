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

-- `15 = 3 * 5` is not deficient `F₂`-perfect.
example : ¬ IsDeficientFkPerfect 2 15 := by
  have h15 : ∏ p ∈ ({3, 5} : Finset ℕ), p = 15 := by decide
  rw [← h15]
  exact not_isDeficientFkPerfect_prod_primes 2 (by decide) {3, 5} (by decide)

-- `105 = 3 * 5 * 7` is not deficient `F₃`-perfect.
example : ¬ IsDeficientFkPerfect 3 105 := by
  have h105 : ∏ p ∈ ({3, 5, 7} : Finset ℕ), p = 105 := by decide
  rw [← h105]
  exact not_isDeficientFkPerfect_prod_primes 3 (by decide) {3, 5, 7} (by decide)

end MathlibExtTest.NumberTheory.FkPerfect
