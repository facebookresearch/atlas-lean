/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.Mertens

/-!
# Tests for Mertens' first and second theorems
-/

@[expose] public section

open Finset ArithmeticFunction Chebyshev

-- `log 3! = Λ(2) + Λ(3)` (the terms `d = 2, 3` each with `⌊3 / d⌋ = 1`).
example : Real.log (Nat.factorial 3 : ℝ) =
    ∑ d ∈ Ioc 0 3, vonMangoldt d * ((3 / d : ℕ) : ℝ) :=
  log_factorial_eq_sum_vonMangoldt_mul_div 3

example : Real.log (Nat.factorial 0 : ℝ) = ∑ d ∈ Ioc 0 0, vonMangoldt d * ((0 / d : ℕ) : ℝ) := by
  simp

-- Boundary `x = 1`: `|0 - 0| ≤ log 4 + 6`.
example : |∑ n ∈ Ioc 0 ⌊(1 : ℝ)⌋₊, vonMangoldt n / (n : ℝ) - Real.log 1| ≤ Real.log 4 + 6 :=
  abs_sum_vonMangoldt_div_sub_log_le 1 le_rfl

example : ∑ p ∈ Nat.primesLE 1, Real.log p / (p : ℝ) ≤ Real.log ((1 : ℕ) : ℝ) + (Real.log 4 + 6) :=
  sum_primesLE_log_div_le 1

example : (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt n / (n : ℝ) - Real.log x)
    =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) :=
  sum_vonMangoldt_div_sub_log_isBigO_one

-- `sum_primesLE_log_div_le` holds at `N = 0`, where the sum is empty.
example : ∑ p ∈ Nat.primesLE 0, Real.log p / (p : ℝ) ≤
    Real.log ((0 : ℕ) : ℝ) + (Real.log 4 + 6) :=
  sum_primesLE_log_div_le 0

/-! ### Mertens' second theorem -/

example : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - Real.log (Real.log x)| ≤ C :=
  abs_sum_primesLE_inv_sub_log_log_le

-- The one-sided upper bound `∑_{p ≤ z} 1/p ≤ log log z + C`.
example : ∃ C : ℝ, ∀ z : ℝ, 2 ≤ z →
    ∑ p ∈ Nat.primesLE ⌊z⌋₊, (p : ℝ)⁻¹ ≤ Real.log (Real.log z) + C := by
  obtain ⟨C, hC⟩ := abs_sum_primesLE_inv_sub_log_log_le
  exact ⟨C, fun z hz => by linarith [(abs_le.mp (hC z hz)).2]⟩

-- The constant is at least `1/2 - log log 2` (take `x = 2`, where the sum is `1/2`).
example (C : ℝ) (hC : ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - Real.log (Real.log x)| ≤ C) :
    1 / 2 - Real.log (Real.log 2) ≤ C := by
  have h := hC 2 le_rfl
  have hs : ∑ p ∈ Nat.primesLE ⌊(2 : ℝ)⌋₊, (p : ℝ)⁻¹ = 1 / 2 := by
    rw [show ⌊(2 : ℝ)⌋₊ = 2 by norm_num, show Nat.primesLE 2 = {2} by decide]
    norm_num
  rw [hs] at h
  exact (le_abs_self _).trans h
