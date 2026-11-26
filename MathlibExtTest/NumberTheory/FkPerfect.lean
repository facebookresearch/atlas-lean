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

-- A counterexample to the printed conclusion `a = k` of Theorem 4:
-- σ₃(4) = 73 = 4³ + 1³ + 2 * 4, with a = 2 ≠ 3 = k.
example : KLNearPerfectWith 3 2 (2 ^ 2) 1 := by
  rw [klNearPerfectWith_prime_pow_iff 2 2 3 2 1 Nat.prime_two (by decide) (by decide)]
  exact ⟨by decide, by decide, rfl, by decide⟩

-- With a = 1 the required range 2 ≤ a fails.
example : ¬ KLNearPerfectWith 2 3 (2 ^ 1) 1 := by
  rw [klNearPerfectWith_prime_pow_iff 2 1 2 3 1 Nat.prime_two (by decide) (by decide)]
  decide

-- Corollary: the exponent is bounded by k.
theorem le_of_klNearPerfectWith_prime_pow (p a k l d : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hl : 1 ≤ l) (h : KLNearPerfectWith k l (p ^ a) d) : a ≤ k :=
  ((klNearPerfectWith_prime_pow_iff p a k l d hp hk hl).mp h).2.1

end MathlibExtTest.NumberTheory.FkPerfect
