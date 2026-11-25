/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.SmoothConsecutiveIntegers

namespace MathlibExtTest.NumberTheory.SmoothConsecutiveIntegers

open MathlibExt.NumberTheory.SmoothConsecutiveIntegersWanted

-- Check the unfolded statement through the public import.
example :
    ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 2 ≤ k →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ a : ℕ, n / 2 ≤ a + 1 ∧ a + k ≤ n ∧
          ∀ j : ℕ, j < k →
            ∀ p ∈ (a + 1 + j).primeFactors, (p : ℝ) ≤ (n : ℝ) ^ ε :=
  conjecture_holds

-- For an odd endpoint, the run may start at the floor of the midpoint.
-- The run 8, 9 has length two and both terms are square-root smooth for n = 17.
example :
    ∃ a : ℕ, (17 : ℕ) / 2 = a + 1 ∧ a + 2 ≤ 17 ∧
      ∀ j : ℕ, j < 2 →
        ∀ p ∈ (a + 1 + j).primeFactors, (p : ℝ) ≤ (17 : ℝ) ^ (1 / 2 : ℝ) := by
  refine ⟨7, by decide, by decide, fun j hj p hp ↦ ?_⟩
  have h8 : (8 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (k := 3) (by decide) Nat.prime_two
  have h9 : (9 : ℕ).primeFactors = {3} :=
    Nat.primeFactors_prime_pow (k := 2) (by decide) Nat.prime_three
  have hp₃ : p ≤ 3 := by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · change p ∈ (8 : ℕ).primeFactors at hp
      have : p = 2 := by simpa [h8] using hp
      omega
    · change p ∈ (9 : ℕ).primeFactors at hp
      have : p = 3 := by simpa [h9] using hp
      omega
  calc
    (p : ℝ) ≤ 3 := by exact_mod_cast hp₃
    _ ≤ (17 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by norm_num)

end MathlibExtTest.NumberTheory.SmoothConsecutiveIntegers
