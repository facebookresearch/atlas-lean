/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimitiveNondeficient

/-! # Tests for the dichotomy for odd primitive non-deficient numbers -/

namespace MathlibExtTest.NumberTheory.PrimitiveNondeficient

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- Conditional form of the dichotomy.
example (n p₁ pK : ℕ) (hno : Odd n) (hn : IsPrimitiveNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors) (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q)
    (hpK : pK ∈ n.primeFactors) (hmax : ∀ q ∈ n.primeFactors, q ≤ pK)
    (hbig : ¬ (pK : ℝ) < Real.sqrt ((∏ q ∈ n.primeFactors, q : ℕ) : ℝ)) :
    ∃ p ∈ n.primeFactors,
      p ^ (n.factorization p + 1) < (n.primeFactors.card + 2 + p₁) * (pK - 1) := by
  rcases max_primeFactor_lt_sqrt_radical_or_exists_pow_lt n p₁ pK hno hn hp₁ hmin
    hpK hmax with h | h
  · exact absurd h hbig
  · exact h

-- Concrete instance: 945 = 3 ^ 3 * 5 * 7 with extremal primes 3 and 7.
example (hn : IsPrimitiveNondeficient 945) :
    (7 : ℝ) < Real.sqrt ((∏ q ∈ (945 : ℕ).primeFactors, q : ℕ) : ℝ) ∨
      ∃ p ∈ (945 : ℕ).primeFactors,
        p ^ ((945 : ℕ).factorization p + 1)
          < ((945 : ℕ).primeFactors.card + 2 + 3) * (7 - 1) := by
  have hpf : (945 : ℕ).primeFactors = {3, 5, 7} := by
    have h945 : (945 : ℕ) = 3 ^ 3 * 5 * 7 := by decide
    rw [h945, Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_pow 3 (by decide), Nat.prime_three.primeFactors,
      Nat.prime_five.primeFactors, (by decide : Nat.Prime 7).primeFactors]
    decide
  have hp₁ : 3 ∈ (945 : ℕ).primeFactors := by rw [hpf]; decide
  have hmin : ∀ q ∈ (945 : ℕ).primeFactors, 3 ≤ q := by
    rw [hpf]
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  have hpK : 7 ∈ (945 : ℕ).primeFactors := by rw [hpf]; decide
  have hmax : ∀ q ∈ (945 : ℕ).primeFactors, q ≤ 7 := by
    rw [hpf]
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  exact max_primeFactor_lt_sqrt_radical_or_exists_pow_lt 945 3 7 ⟨472, rfl⟩ hn hp₁ hmin
    hpK hmax

end MathlibExtTest.NumberTheory.PrimitiveNondeficient
