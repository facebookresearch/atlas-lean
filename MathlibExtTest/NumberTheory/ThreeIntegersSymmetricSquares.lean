/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquares

/-! # Tests for sums of two squares and triples with square symmetric functions -/

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

example : IsSumTwoSquaresℚ 0 :=
  ⟨0, 0, by norm_num⟩

-- The denominator can be nonintegral and a square summand can vanish.
example : IsSumTwoSquaresℚ (1 / (5 / 9)) :=
  sum_two_squares_div_sum_two_squaresℚ (by norm_num) (by norm_num)
    ⟨1, 0, by norm_num⟩ ⟨1 / 3, -2 / 3, by norm_num⟩

-- Both the entry and the second elementary symmetric function can vanish.
example : IsSumTwoSquaresℚ 0 ∧ IsSumTwoSquaresℚ (1 / 9) := by
  have h : HasSquareElementarySymmetricFunctionsℚ 0 0 (1 / 9) :=
    ⟨⟨1 / 3, by norm_num⟩, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩
  obtain ⟨h₀, _, h₁, _⟩ :=
    isSumTwoSquaresℚ_of_hasSquareElementarySymmetricFunctionsℚ_and_scaling h
  exact ⟨h₀, h₁⟩

-- Dividing (45, 64, 180) by four makes one entry nonintegral.
-- The integer solution obtained by rescaling still has C = 4A.
example : ∃ A B C : ℤ, A ≠ 0 ∧ C = 4 * A ∧ HasSquareElementarySymmetricFunctions A B C ∧
    IsSumTwoSquaresℤ A ∧ IsSumTwoSquaresℤ B ∧ IsSumTwoSquaresℤ C := by
  have h : HasSquareElementarySymmetricFunctionsℚ (45 / 4) 16 45 :=
    ⟨⟨17 / 2, by norm_num⟩, ⟨75 / 2, by norm_num⟩, ⟨90, by norm_num⟩⟩
  obtain ⟨_, _, _, k, A, B, C, hk, hA, _, hC, hs, sums⟩ :=
    isSumTwoSquaresℚ_of_hasSquareElementarySymmetricFunctionsℚ_and_scaling h
  refine ⟨A, B, C, ?_, ?_, hs, sums⟩
  · exact_mod_cast hA.symm ▸ mul_ne_zero hk (by norm_num : (45 / 4 : ℚ) ≠ 0)
  · exact_mod_cast (show (C : ℚ) = 4 * A by rw [hC, hA]; ring)

-- A nondegenerate member of the family.
example : HasSquareElementarySymmetricFunctions 45 180 64 :=
  hasSquareElementarySymmetricFunctions_family33 2 1

-- Pairwise products of a member of the family keep square symmetric functions.
example : HasSquareElementarySymmetricFunctions (45 * 180) (180 * 64) (64 * 45) :=
  hasSquareElementarySymmetricFunctions_pairwise_products
    (hasSquareElementarySymmetricFunctions_family33 2 1)

-- The zero triple is preserved by pairwise products.
example : HasSquareElementarySymmetricFunctions (0 * 0) (0 * 0) (0 * 0) :=
  hasSquareElementarySymmetricFunctions_pairwise_products
    ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩

-- Opposite parameters make the first two entries vanish.
example : HasSquareElementarySymmetricFunctions 0 0 4 := by
  convert hasSquareElementarySymmetricFunctions_family33 (-1) 1 using 1 <;> norm_num

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
