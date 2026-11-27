/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingGeometricSumDifferenceOfSquares

open MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

-- At the least admissible base and exponent, the sum is 7.
example :
    (∑ j ∈ Finset.range 3, (-1 : ℤ) ^ j * (3 : ℤ) ^ (1 * j)) = 7 ∧
      (7 : ℤ) = 4 ^ 2 - 3 ^ 2 := by decide

-- For exponent three, the sum is 703; check this without the theorem.
example :
    (∑ j ∈ Finset.range 3, (-1 : ℤ) ^ j * (3 : ℤ) ^ (3 * j)) = 703 ∧
      (703 : ℤ) = 352 ^ 2 - 351 ^ 2 := by decide

example : ∃ a b : ℤ, (7 : ℤ) = a ^ 2 - b ^ 2 := by
  have hs : (∑ j ∈ Finset.range 3, (-1 : ℤ) ^ j * (3 : ℤ) ^ (1 * j)) = 7 := by decide
  rw [← hs]
  exact altGeomSum_eq_sq_sub_sq 3 1 Nat.prime_three rfl ⟨0, rfl⟩ (by decide)
