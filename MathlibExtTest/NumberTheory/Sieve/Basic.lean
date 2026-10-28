/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Sieve.Basic

/-!
# Tests for the sifting product
-/

@[expose] public section

open Nat

/-! ### Concrete values -/

example : siftingPrimorial (fun _ => True) 5 = 30 := by decide
example : siftingPrimorial (fun p => p % 2 = 1) 7 = 105 := by decide
example : siftingPrimorial (fun p => p % 4 = 1) 20 = 5 * 13 * 17 := by decide

/-! ### Boundary values -/

example (P : ℕ → Prop) [DecidablePred P] : siftingPrimorial P 0 = 1 := by
  rw [siftingPrimorial, show (0 : ℕ).primesLE = ∅ by decide]
  simp
example (P : ℕ → Prop) [DecidablePred P] : siftingPrimorial P 1 = 1 := by
  rw [siftingPrimorial, show (1 : ℕ).primesLE = ∅ by decide]
  simp
example (z : ℕ) : siftingPrimorial (fun _ => False) z = 1 := by
  simp [siftingPrimorial]

/-! ### Agreement with Mathlib and basic API -/

example (z : ℕ) : siftingPrimorial (fun _ => True) z = primorial z := siftingPrimorial_true z
example : Squarefree (siftingPrimorial (fun p => p % 2 = 1) 100) :=
  squarefree_siftingPrimorial _ _
example : (siftingPrimorial (fun p => p % 2 = 1) 7).primeFactors = {3, 5, 7} := by
  rw [primeFactors_siftingPrimorial]
  decide
example : 3 ∣ siftingPrimorial (fun p => p % 2 = 1) 7 :=
  (Nat.prime_three.dvd_siftingPrimorial_iff).mpr ⟨by norm_num, by norm_num⟩
example : ¬ 2 ∣ siftingPrimorial (fun p => p % 2 = 1) 7 := fun h =>
  absurd ((Nat.prime_two.dvd_siftingPrimorial_iff).mp h).2 (by norm_num)

/-! ### Totient products -/

example : ((Nat.totient 12 : ℕ) : ℝ) = 12 * ∏ p ∈ (12 : ℕ).primeFactors, (1 - (p : ℝ)⁻¹) :=
  cast_totient_eq_mul_prod_one_sub_inv 12

-- Boundary `n = 0`: both sides vanish.
example : ((Nat.totient 0 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) * ∏ p ∈ (0 : ℕ).primeFactors, (1 - (p : ℝ)⁻¹) :=
  cast_totient_eq_mul_prod_one_sub_inv 0

example : ∏ m ∈ Finset.Ioc 1 1, (1 - (((m : ℕ) : ℝ) ^ 2)⁻¹) = ((1 : ℝ) + 1) / (2 * 1) := by
  simp

example : ∏ m ∈ Finset.Ioc 1 3, (1 - (((m : ℕ) : ℝ) ^ 2)⁻¹) = 2 / 3 := by
  rw [prod_Ioc_one_sub_inv_sq 3 (by norm_num)]
  norm_num

example : (6 : ℝ) / totient 6 ≤ 2 * ∏ p ∈ (6 : ℕ).primeFactors, (1 + (p : ℝ)⁻¹) :=
  div_totient_le_two_mul_prod_one_add_inv (by norm_num)

-- Euler's product over `ℚ` is already Mathlib's `Nat.totient_eq_mul_prod_factors`.
example (n : ℕ) : (totient n : ℚ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) :=
  Nat.totient_eq_mul_prod_factors n
