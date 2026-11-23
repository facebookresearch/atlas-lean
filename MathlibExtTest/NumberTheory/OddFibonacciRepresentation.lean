/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Fib.Zeckendorf
import MathlibExt.NumberTheory.OddFibonacciRepresentation

open Finset MetaMathlibExt

-- The forbidden units pattern rules out 5 = 2 · 2 + 1, forcing a carry into the 5-place.
example : ∃ a : ℕ → ℕ, 5 = ∑ k ∈ range 3, a k * Nat.fib (2 * k + 1) ∧
    (a 0, a 1, a 2) = (0, 0, 1) := by
  obtain ⟨n, a, hlo, hhi, hsum, h₀, hbound, hlow, _⟩ :=
    exists_odd_fib_representation (t := 5) (by decide)
  have hlo' : 2 * n + 1 ≤ 5 := Nat.le_greatestFib.mpr hlo
  have hhi' : 5 < 2 * n + 3 := Nat.greatestFib_lt.mpr hhi
  obtain rfl : n = 2 := by omega
  refine ⟨a, hsum, ?_⟩
  simp [sum_range_succ, Nat.fib_add_two] at hsum
  have h₁ := hbound 1 le_rfl
  simp only [Prod.mk.injEq]
  omega

-- The adjacent-twos restriction excludes 14 = 2 · 5 + 2 · 2, leaving 14 = 13 + 1.
example : ∃ a : ℕ → ℕ, 14 = ∑ k ∈ range 4, a k * Nat.fib (2 * k + 1) ∧
    (a 0, a 1, a 2, a 3) = (1, 0, 0, 1) := by
  obtain ⟨n, a, hlo, hhi, hsum, h₀, hbound, _, hadj⟩ :=
    exists_odd_fib_representation (t := 14) (by decide)
  have hlo' : 2 * n + 1 ≤ 7 := Nat.le_greatestFib.mpr hlo
  have hhi' : 7 < 2 * n + 3 := Nat.greatestFib_lt.mpr hhi
  obtain rfl : n = 3 := by omega
  refine ⟨a, hsum, ?_⟩
  simp [sum_range_succ, Nat.fib_add_two] at hsum
  have h₁ := hbound 1 le_rfl
  have h₂ := hbound 2 (by decide)
  have hpair : ¬ (a 2 = 2 ∧ a 1 = 2) := hadj 1
  have h₃ : a 3 = 1 := by
    by_cases h : a 3 = 0 <;> omega
  rw [h₃] at hsum ⊢
  simp only [Prod.mk.injEq, and_true]
  omega
