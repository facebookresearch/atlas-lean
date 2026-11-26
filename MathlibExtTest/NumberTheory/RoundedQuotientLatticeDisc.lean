/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RoundedQuotientLatticeDisc

namespace MetaMathlibExt

-- At radius zero, only the origin is counted.
example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * (0 : ℤ)} = 1 := by
  have h : 4 * roundQuotientOddCount 0 + 4 * 0 + 1 = 1 := by decide +kernel
  exact (card_lattice_disc_two_mul (n := 0)).trans h

-- The four points (±1, ±1) on the boundary are included in the nine points.
example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * (1 : ℤ)} = 9 := by
  have h : 4 * roundQuotientOddCount 1 + 4 * 1 + 1 = 9 := by decide +kernel
  exact (card_lattice_disc_two_mul (n := 1)).trans h

-- Dent and Shor, Example 18: the closed disc of radius 6 contains 113 points.
example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * (18 : ℤ)} = 113 := by
  have h : 4 * roundQuotientOddCount 18 + 4 * 18 + 1 = 113 := by decide +kernel
  exact (card_lattice_disc_two_mul (n := 18)).trans h

-- The empty sequence gives an integer lower bound of -1, not a truncated subtraction.
example : -1 ≤ (roundQuotientOddCount 1 : ℤ) := by
  have h₀ : roundQuotientOddCount 0 = 0 := by decide +kernel
  simpa only [h₀, Nat.cast_zero, zero_sub, zero_add] using
    roundQuotientOddCount_sub_one_le_succ (n := 0)

-- The bound is sharp: the count can decrease by exactly one.
example : (roundQuotientOddCount 6 : ℤ) = (roundQuotientOddCount 5 : ℤ) - 1 := by
  have h₅ : roundQuotientOddCount 5 = 4 := by decide +kernel
  have h₆ : roundQuotientOddCount 6 = 3 := by decide +kernel
  refine le_antisymm ?_ (roundQuotientOddCount_sub_one_le_succ (n := 5))
  rw [h₅, h₆]
  decide

-- At k = 4, 6/k = 3/2 rounds up to 2; at k = 6 it rounds to 1.
example : round ((6 : ℚ) / 4) = 2 ∧ round ((6 : ℚ) / 6) = 1 := by decide +kernel

-- The same comparison in naturals puts the +1 on the successor side.
example (n : ℕ) : roundQuotientOddCount n ≤ roundQuotientOddCount (n + 1) + 1 := by
  have h := roundQuotientOddCount_sub_one_le_succ (n := n)
  omega

end MetaMathlibExt
