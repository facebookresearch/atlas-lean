/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PolygonalSumModPrimePow
import MathlibExt.NumberTheory.PolygonalNumber

/-! # Tests for sums of two polygonal numbers modulo prime powers -/

open MetaMathlibExt

-- For square numbers, the prime supplied by the theorem represents every
-- positive integer as a sum of two positive squares modulo prime powers.
example : ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ ¬ p ∣ 2 ∧
    ∀ k n : ℕ, 0 < k → 0 < n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 ≡ n [MOD p ^ k] := by
  obtain ⟨p, hp, hp4, hpdvd, h⟩ :=
    exists_prime_polygonal_add_polygonal_modEq_prime_pow 4 (by decide)
  refine ⟨p, hp, hp4, hpdvd, fun k n hk hn => ?_⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := h k n hk hn
  simp only [Nat.polygonalNumber_four] at hxy
  exact ⟨x, y, hx, hy, hxy⟩

-- At the second prime power, the witnesses for pentagonal numbers are positive
-- and their sum has the required residue.
example : ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ ¬ p ∣ 3 ∧
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
      Nat.polygonalNumber 5 x + Nat.polygonalNumber 5 y ≡ 10 [MOD p ^ 2] := by
  obtain ⟨p, hp, hp4, hpdvd, h⟩ :=
    exists_prime_polygonal_add_polygonal_modEq_prime_pow 5 (by decide)
  obtain ⟨x, y, hx, hy, hxy⟩ := h 2 10 (by decide) (by decide)
  exact ⟨p, hp, hp4, hpdvd, x, y, hx, hy, hxy⟩

-- The prime for hexagonal numbers does not divide `s - 2 = 4`.
example : ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ ¬ p ∣ 4 ∧
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
      Nat.polygonalNumber 6 x + Nat.polygonalNumber 6 y ≡ 1 [MOD p] := by
  obtain ⟨p, hp, hp4, hpdvd, h⟩ :=
    exists_prime_polygonal_add_polygonal_modEq_prime_pow 6 (by decide)
  obtain ⟨x, y, hx, hy, hxy⟩ := h 1 1 (by decide) (by decide)
  exact ⟨p, hp, hp4, hpdvd, x, y, hx, hy, by simpa using hxy⟩
