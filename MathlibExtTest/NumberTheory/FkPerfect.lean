/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfect
import Mathlib.Tactic.NormNum

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

-- A concrete instance with `k = 2`, `p₁ = 3`, `p₂ = 5` and `a = 1`.
example : ¬ IsNearFkPerfect 2 (3 ^ 1 * 5) :=
  not_isNearFkPerfect_prime_pow_mul 2 3 5 1 (by decide) (by decide) (by decide)
    (⟨1, rfl⟩ : Odd (3 : ℕ)) (⟨2, rfl⟩ : Odd (5 : ℕ)) (by decide)

-- A concrete instance with `k = 3`, `p₁ = 5`, `p₂ = 7` and `a = 2`.
example : ¬ IsNearFkPerfect 3 (5 ^ 2 * 7) :=
  not_isNearFkPerfect_prime_pow_mul 3 5 7 2 (by decide) (by decide) (by decide)
    (⟨2, rfl⟩ : Odd (5 : ℕ)) (⟨3, rfl⟩ : Odd (7 : ℕ)) (by decide)

-- Fixing the primes gives a corollary for every `k > 1` and every exponent.
example (k a : ℕ) (hk : 1 < k) : ¬ IsNearFkPerfect k (3 ^ a * 5) :=
  not_isNearFkPerfect_prime_pow_mul k 3 5 a hk (by decide) (by decide)
    (⟨1, rfl⟩ : Odd (3 : ℕ)) (⟨2, rfl⟩ : Odd (5 : ℕ)) (by decide)

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

-- Primes are not `[k, ℓ]`-near-perfect for `1 ≤ ℓ`, at zero and positive exponents.
example : ¬ IsKLNearPerfect 0 1 2 :=
  not_isKLNearPerfect_of_prime 0 1 2 (by decide) (by decide)

example : ¬ IsKLNearPerfect 2 3 5 :=
  not_isKLNearPerfect_of_prime 2 3 5 (by decide) (by decide)

-- At `ℓ = 0` every prime is `[k, 0]`-near-perfect with divisor `1`.
example (k p : ℕ) (hp : p.Prime) : IsKLNearPerfect k 0 p := by
  refine ⟨1, one_dvd p, hp.one_lt, ?_⟩
  simp only [hp.sum_divisors, one_pow, zero_mul, add_zero]

-- `18` is `[1, 1]`-near-perfect, and twice a power of `5` is never `[1, ℓ]`-near-perfect.
example : IsKLNearPerfect 1 1 18 :=
  (isKLNearPerfect_one_two_mul_prime_pow 3 2 1 (by decide) (by decide) (by decide)).1

example (a l : ℕ) (hl : 1 ≤ l) : ¬ IsKLNearPerfect 1 l (2 * 5 ^ a) := by
  intro h
  have heq :=
    (isKLNearPerfect_one_two_mul_prime_pow 5 a l (by decide) (by decide) hl).2 h
  have hpow : (5 : ℕ) ^ a = 9 := by omega
  cases a with
  | zero => norm_num at hpow
  | succ a =>
    have hdiv : 5 ∣ (9 : ℕ) := by
      rw [← hpow]
      exact dvd_pow_self 5 (by omega)
    norm_num at hdiv

-- `3 ^ 1 * 5 ^ 2` is not deficient `F₂`-perfect: `1 + 2` is odd.
example : ¬ IsDeficientFkPerfect 2 (3 ^ 1 * 5 ^ 2) :=
  not_isDeficientFkPerfect_pow_mul_pow 2 3 5 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))

-- `3 ^ 1 * 5 ^ 1` is not deficient `F₃`-perfect: both exponents are odd.
example : ¬ IsDeficientFkPerfect 3 (3 ^ 1 * 5 ^ 1) :=
  not_isDeficientFkPerfect_pow_mul_pow 3 3 5 1 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inr ⟨by decide, by decide⟩)

-- Eight is a prime power, so it is neither deficient `F`-perfect nor near `F`-perfect.
example : ¬ IsDeficientFPerfect 8 ∧ ¬ IsNearFPerfect 8 := by
  simpa using prime_pow_not_fPerfect 2 3 Nat.prime_two

-- Nine is a prime power, so it is not deficient `F`-perfect.
example : ¬ IsDeficientFPerfect 9 := by
  simpa using (prime_pow_not_fPerfect 3 2 (by decide)).1

-- Every prime is a prime power with exponent one.
example (p : ℕ) (hp : p.Prime) : ¬ IsDeficientFPerfect p ∧ ¬ IsNearFPerfect p := by
  simpa using prime_pow_not_fPerfect p 1 hp

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

-- Twice three is not `[k,ℓ]`-near-perfect.
example (k l : ℕ) (hl : 1 ≤ l) : ¬ IsKLNearPerfect k l 6 :=
  not_isKLNearPerfect_two_mul_prime (k := k) (l := l) (p := 3)
    (hl := hl) (hp := by decide) (hpo := ⟨1, rfl⟩)

example : ¬ IsKLNearPerfect 2 1 10 :=
  not_isKLNearPerfect_two_mul_prime (k := 2) (l := 1) (p := 5)
    (hl := by decide) (hp := by decide) (hpo := ⟨2, rfl⟩)

end MathlibExtTest.NumberTheory.FkPerfect
