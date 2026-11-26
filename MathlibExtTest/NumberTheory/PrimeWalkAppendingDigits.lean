/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Monotone.Basic
import MathlibExt.NumberTheory.PrimeWalkAppendingDigits

open MetaMathlibExt

-- At the smallest prime, removing the first appended block recovers the seed.
example : ∃ q n k : ℕ, q.Prime ∧ 0 < n ∧ 0 < k ∧ k < 10 ^ n ∧ q / 10 ^ n = 2 := by
  obtain ⟨p, hp₀, hp, hstep⟩ := exists_prime_walk_appending_decimal_digits 2 Nat.prime_two
  obtain ⟨n, k, hn, hk, hkn, heq⟩ := hstep 0
  refine ⟨p 1, n, k, hp 1, hn, hk, hkn, ?_⟩
  have hpow : 0 < (10 : ℕ) ^ n := Nat.pow_pos (by decide)
  rw [heq, hp₀, Nat.mul_add_div hpow, Nat.div_eq_of_lt hkn, add_zero]

-- The steps from 5 are strictly increasing, so the walk does not revisit a prime.
example : ∃ p : ℕ → ℕ, p 0 = 5 ∧ (∀ i, (p i).Prime) ∧ StrictMono p := by
  obtain ⟨p, hp₀, hp, hstep⟩ := exists_prime_walk_appending_decimal_digits 5 (by decide)
  refine ⟨p, hp₀, hp, strictMono_nat_of_lt_succ fun i => ?_⟩
  obtain ⟨n, k, _, hk, _, heq⟩ := hstep i
  have hpow : 0 < (10 : ℕ) ^ n := Nat.pow_pos (by decide)
  rw [heq]
  exact (Nat.le_mul_of_pos_left _ hpow).trans_lt (Nat.lt_add_of_pos_right hk)
