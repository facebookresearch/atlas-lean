/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BarryTriangleExplicitFormulas

open MetaMathlibExt

-- On the diagonal the only exponent tuple is the zero tuple.
example (a : ℕ) (ha : 2 ≤ a) : barryTriangleAux 0 a a = 1 := by
  rw [barryTriangleAux_eq_sum_antidiagonalTuple a a ha le_rfl]
  simp [Finset.Nat.antidiagonalTuple_zero_right]

-- In column two there is a single weight, equal to one.
example (d : ℕ) : barryTriangleAux 0 (d + 2) 2 = 1 := by
  rw [barryTriangleAux_eq_sum_antidiagonalTuple _ _ (by decide) (by omega)]
  simp

-- The three weights in column four are 3, 4 and 3.
example : barryTriangleAux 0 6 4 = 67 := by
  rw [barryTriangleAux_eq_sum_antidiagonalTuple _ _ (by decide) (by decide)]
  decide

-- At n = a = 2 the matrix is 1 × 1 and the exponent is zero.
example : barryTriangleAux 0 2 2 = 1 := by
  rw [barryTriangleAux_eq_matrix_pow _ _ (by decide) (by decide)]
  decide

-- The 1 × 1 matrix also gives one for a positive exponent.
example : barryTriangleAux 0 7 2 = 1 := by
  rw [barryTriangleAux_eq_matrix_pow _ _ (by decide) (by decide)]
  decide

-- At n = a = 4 the bottom-left entry requires two subdiagonal steps.
example : barryTriangleAux 0 4 4 = 1 := by
  rw [barryTriangleAux_eq_matrix_pow _ _ (by decide) (by decide)]
  decide

-- Away from the diagonal both kinds of steps contribute (Table 1).
example : barryTriangleAux 0 6 4 = 67 := by
  rw [barryTriangleAux_eq_matrix_pow _ _ (by decide) (by decide)]
  decide
