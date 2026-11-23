/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Enumerative.Catalan.Bounds
import Mathlib.Combinatorics.Enumerative.Catalan.Tree

example (n : ℕ) : catalan n ≤ 4 ^ n := catalan_le_four_pow n

example : catalan 0 ≤ 4 ^ 0 := catalan_le_four_pow 0

example : catalan 4 = 14 := by
  simp [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

example : catalan 4 ≤ 256 := catalan_le_four_pow 4

example (n : ℕ) : (BinaryTree.treesOfNumNodesEq n).card ≤ 4 ^ n := by
  rw [BinaryTree.treesOfNumNodesEq_card_eq_catalan]
  exact catalan_le_four_pow n

example : (BinaryTree.treesOfNumNodesEq 3).card = 5 := by
  rw [BinaryTree.treesOfNumNodesEq_card_eq_catalan, catalan_three]

example (n : ℕ) : (catalan n : ℚ) * (1 / 8 : ℚ) ^ n ≤ (1 / 2 : ℚ) ^ n := by
  have hc : (catalan n : ℚ) ≤ (4 : ℚ) ^ n := by
    simpa using (Nat.cast_le.mpr (catalan_le_four_pow n) :
      (catalan n : ℚ) ≤ ((4 ^ n : ℕ) : ℚ))
  calc
    (catalan n : ℚ) * (1 / 8 : ℚ) ^ n ≤ (4 : ℚ) ^ n * (1 / 8 : ℚ) ^ n :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (by norm_num) n)
    _ = (4 * (1 / 8) : ℚ) ^ n := (mul_pow _ _ _).symm
    _ = (1 / 2 : ℚ) ^ n := by
      norm_num

#print axioms catalan_le_four_pow
