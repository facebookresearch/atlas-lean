/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Finset.Insert
import MathlibExt.NumberTheory.OddMultiplePrimeHalfSets

/-! # Tests for odd multiples of half the predecessor of a prime -/

open MetaMathlibExt

-- The empty family allows the boundary witness from p = 13 and m = 0.
example : (∃ p m : ℕ, p.Prime ∧ 13 ≤ p ∧ p % 4 = 1 ∧ 6 = ((p - 1) / 2) * (2 * m + 1)) ∧
    ∀ q ∈ (∅ : Finset ℕ), ¬∃ m, 6 = ((q - 1) / 2) * (2 * m + 1) := by
  exact ⟨⟨13, 0, by decide, by decide, rfl, rfl⟩, by simp⟩

-- The odd multiples for 13 and 17 are the classes 6 mod 12 and 8 mod 16.
example : ∃ k : ℕ, (∃ p m : ℕ, p.Prime ∧ 13 ≤ p ∧ p % 4 = 1 ∧
    k = ((p - 1) / 2) * (2 * m + 1)) ∧ k % 12 ≠ 6 ∧ k % 16 ≠ 8 := by
  have hS : ∀ p ∈ ({13, 17} : Finset ℕ), p.Prime ∧ 13 ≤ p ∧ p % 4 = 1 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> decide
  obtain ⟨k, hk, hmiss⟩ := odd_multiple_prime_half_sets_not_finitely_coverable {13, 17} hS
  refine ⟨k, hk, fun h => hmiss 13 (by decide) ⟨k / 12, ?_⟩,
    fun h => hmiss 17 (by decide) ⟨k / 16, ?_⟩⟩ <;> omega
