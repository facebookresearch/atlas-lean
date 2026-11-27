/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeometricSumsTwoSquares

open MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

-- The least admissible base and exponent give the sum 13.
example : ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 := by
  have hs : ∑ j ∈ Finset.range 3, 3 ^ (1 * j) = 13 := by decide
  rw [← hs]
  exact (geomSum_pythagorean 3 1 Nat.prime_three rfl ⟨0, rfl⟩ (by decide)).2

-- For exponent five the sum is composite: 59293 = 13 * 4561.
example (q : ℕ) (hq : q.Prime) (hd : q ∣ 59293) : q % 4 = 1 := by
  have hs : ∑ j ∈ Finset.range 3, 3 ^ (5 * j) = 59293 := by decide
  have h := (geomSum_pythagorean 3 5 Nat.prime_three rfl ⟨2, rfl⟩ (by decide)).1 q hq
  rw [hs] at h
  apply (h hd).resolve_left
  rintro rfl
  exact (by decide : ¬2 ∣ 59293) hd

-- The length-nine sum is 9841 = 60² + 79².
example : (∑ j ∈ Finset.range (3 ^ 2), (3 : ℤ) ^ (1 * j)) = 60 ^ 2 + 79 ^ 2 := by
  decide

example : ∃ a b : ℤ, 9841 = a ^ 2 + b ^ 2 := by
  have hs : (∑ j ∈ Finset.range (3 ^ 2), (3 : ℤ) ^ (1 * j)) = 9841 := by decide
  rw [← hs]
  exact geomSumPow_eq_sq_add_sq 3 1 2 Nat.prime_three rfl ⟨0, rfl⟩ (by decide) (by decide)
