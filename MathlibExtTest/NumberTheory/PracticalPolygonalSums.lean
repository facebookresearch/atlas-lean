/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PracticalPolygonalSums
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! # Tests for sums of practical and polygonal numbers -/

open MetaMathlibExt

-- At the smallest exponent the interval forces the root to be 1.
example (n : ℕ) (hn : 0 < n) : 1 ≡ 8 * n + 1 [MOD 8] := by
  obtain ⟨x, hlo, hhi, hsq⟩ := exists_sq_modEq_eight_mul_add_one 1 n (by decide) hn
  have hx : x = 1 := by omega
  subst x
  exact hsq

-- The upper endpoint is necessary for 17 modulo 32.
example : (∃ x : ℕ, x ≤ 7 ∧ x ^ 2 ≡ 17 [MOD 32]) ∧
    ¬ ∃ x : ℕ, x < 7 ∧ x ^ 2 ≡ 17 [MOD 32] := by
  constructor
  · obtain ⟨x, _, hhi, hsq⟩ := exists_sq_modEq_eight_mul_add_one 3 2 (by decide) (by decide)
    exact ⟨x, hhi, hsq⟩
  · rintro ⟨x, hx, hsq⟩
    interval_cases x <;> norm_num [Nat.ModEq] at hsq

-- For pentagonal numbers modulo 3 the quadratic coefficient vanishes.
example (n : ℕ) (hn : 0 < n) : ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
    Nat.polygonalNumber 5 x + Nat.polygonalNumber 5 y ≡ n [MOD 3] ∧ x + y ≡ n [MOD 3] := by
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    exists_polygonal_add_polygonal_modEq_prime 3 n 5 (by decide) (by decide) hn (by decide)
  have hlin (k : ℕ) : Nat.polygonalNumber 5 k ≡ k [MOD 3] := by
    change 3 * k.choose 2 + k ≡ k [MOD 3]
    simp [Nat.ModEq, Nat.add_mod]
  exact ⟨x, y, hx, hy, hxy, ((hlin x).add (hlin y)).symm.trans hxy⟩

-- At the smallest odd prime, representing zero by squares requires the zero residue.
example : (∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 ≡ 0 [MOD 3]) ∧
    ¬ ∃ x y : ℕ, 0 < x ∧ x < 3 ∧ 0 < y ∧ y < 3 ∧ x ^ 2 + y ^ 2 ≡ 0 [MOD 3] := by
  constructor
  · simpa only [Nat.polygonalNumber_four, Nat.ModEq] using
      exists_polygonal_add_polygonal_modEq_prime 3 3 4 (by decide) (by decide) (by decide)
        (by decide)
  · rintro ⟨x, y, hx, hx', hy, hy', hxy⟩
    interval_cases x <;> interval_cases y <;> norm_num [Nat.ModEq] at hxy

-- The upper endpoint of the classification is practical.
example : IsPracticalNumber 2 := by
  refine ⟨by decide, fun m hm hm' ↦ ⟨{m}, ?_, by simp⟩⟩
  obtain rfl | rfl : m = 1 ∨ m = 2 := by omega
  · simp
  · simp

-- The first even integer above 2 divisible by neither 3 nor 4 is 10.
example : ¬ IsPracticalNumber 10 := by
  intro h
  have := isPracticalNumber_eq_one_or_two 10 h (by decide) (by decide)
  omega

-- For square numbers, evaluating at the first admissible index bounds the coefficient from below.
example (c : ℕ) : ∃ A : ℕ, 2 * (2 * c) ^ 2 ≤ A ∧
    ∀ x : ℕ, 1 ≤ x → 2 * (2 * c * x) ^ 2 ≤ A * x ^ 2 := by
  obtain ⟨A, hA⟩ := exists_two_polygonal_two_mul_le_mul_sq 4 c (by decide)
  simp only [Nat.polygonalNumber_four] at hA
  exact ⟨A, by simpa using hA 1 le_rfl, hA⟩
