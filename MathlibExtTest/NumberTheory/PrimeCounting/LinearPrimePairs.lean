/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.LinearPrimePairs

/-!
# Tests for the upper bound on primes `p` with `kp + 1` prime
-/

@[expose] public section

open Finset Nat

-- The primes `p ≤ 20` with `2p + 1` prime (Sophie Germain primes): `2, 3, 5, 11`.
example : ((primesLE 20).filter (fun p : ℕ => (2 * p + 1).Prime)).card = 4 := by decide

-- The constant is uniform in `k`; instantiate at `k = 2` and at `k = 6`.
example : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    (((primesLE ⌊x⌋₊).filter (fun p : ℕ => (2 * p + 1).Prime)).card : ℝ) ≤
      C * x / Real.log x ^ 2 * ∏ p ∈ (2 : ℕ).primeFactors, (1 + (p : ℝ)⁻¹) := by
  obtain ⟨C, hC⟩ := card_filter_prime_mul_add_one_prime_le
  exact ⟨C, hC 2 even_two le_rfl⟩

example : ∃ C : ℝ, ∀ k : ℕ, Even k → 2 ≤ k → ∀ x : ℝ, 2 ≤ x →
    (((primesLE ⌊x⌋₊).filter (fun p : ℕ => (k * p + 1).Prime)).card : ℝ) ≤
      C * x / Real.log x ^ 2 * ∏ p ∈ k.primeFactors, (1 + (p : ℝ)⁻¹) :=
  card_filter_prime_mul_add_one_prime_le
