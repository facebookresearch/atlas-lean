/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences
import Mathlib.NumberTheory.Zsqrtd.Basic

/-! # Tests for `MathlibExt.Algebra.DeepPowerSumCongruences` -/

namespace MathlibExtTest.DeepPowerSumCongruences

open MetaMathlibExt

/-- In any commutative ring the ideal `(p)` satisfies `a ^ p ∈ p (p)`: for `a = x p`,
`a ^ p = p (x ^ p p ^ (p - 1))` and `p ^ (p - 1) ∈ (p)` as `p - 1 ≥ 1`. -/
private theorem pow_prime_mem_span_prime {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] :
    ∀ a ∈ Ideal.span {(p : B)}, ∃ c ∈ Ideal.span {(p : B)}, a ^ p = (p : B) * c := by
  have hp : p.Prime := Fact.out
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  refine ⟨x ^ (k + 1) * ((k + 1 : ℕ) : B) ^ k, Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _
    (Ideal.mem_span_singleton_self _) _ (by have := hp.two_le; omega)), by ring⟩

-- Test section: the criterion holds. For the ideal `(p)` of any commutative ring, the theorem
-- turns the single condition above into `a ^ n ∈ p ^ v_p(n!) (p)` for every `n ≥ 1`.
example {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] :
    ∀ n : ℕ, 1 ≤ n → ∀ a ∈ Ideal.span {(p : B)}, ∃ c ∈ Ideal.span {(p : B)},
      a ^ n = (p : B) ^ padicValNat p n.factorial * c :=
  (pow_mem_prime_pow_padicValNat_factorial_iff _).2 pow_prime_mem_span_prime

-- The hypothesis `1 ≤ n` cannot be dropped: for the ideal `(2)` of `ℤ` every `n ≥ 1` works, but
-- `n = 0` would need `a ^ 0 = 1 ∈ 2 ^ v_2(0!) (2) = (2)`.
example : (∀ n : ℕ, 1 ≤ n → ∀ a ∈ Ideal.span {((2 : ℕ) : ℤ)}, ∃ c ∈ Ideal.span {((2 : ℕ) : ℤ)},
      a ^ n = ((2 : ℕ) : ℤ) ^ padicValNat 2 n.factorial * c) ∧
    ¬ ∃ c ∈ Ideal.span {((2 : ℕ) : ℤ)},
      (2 : ℤ) ^ 0 = ((2 : ℕ) : ℤ) ^ padicValNat 2 (Nat.factorial 0) * c := by
  refine ⟨(pow_mem_prime_pow_padicValNat_factorial_iff _).2 pow_prime_mem_span_prime, ?_⟩
  rintro ⟨c, hc, h⟩
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  simp at h
  omega

-- Test section: the criterion fails. The unit ideal of `ℤ` does not have `1 ^ 3 ∈ 3 ℤ`, so by the
-- theorem some `a ^ n` is not in `3 ^ v_3(n!) ℤ`.
example : ¬ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ (⊤ : Ideal ℤ), ∃ c ∈ (⊤ : Ideal ℤ),
    a ^ n = ((3 : ℕ) : ℤ) ^ padicValNat 3 n.factorial * c := by
  rw [pow_mem_prime_pow_padicValNat_factorial_iff]
  intro h
  obtain ⟨c, -, hc⟩ := h 1 Submodule.mem_top
  simp at hc
  omega

-- In `ℤ√2` the ideal `(√2)` fails the criterion for `p = 2`: `√2 ^ 2 = 2`, but every element of
-- `2 (√2)` has rational part divisible by `4`. So, by the theorem, some power of an element of
-- `(√2)` is not in `2 ^ v_2(n!) (√2)`.
example : ¬ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ Ideal.span {(Zsqrtd.sqrtd : ℤ√2)},
    ∃ c ∈ Ideal.span {(Zsqrtd.sqrtd : ℤ√2)},
      a ^ n = ((2 : ℕ) : ℤ√2) ^ padicValNat 2 n.factorial * c := by
  rw [pow_mem_prime_pow_padicValNat_factorial_iff]
  intro h
  obtain ⟨c, hc, hsq⟩ := h _ (Ideal.mem_span_singleton_self _)
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  have hre := congrArg Zsqrtd.re hsq
  simp [pow_two] at hre
  omega

end MathlibExtTest.DeepPowerSumCongruences
