/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.SimpleGraph.RookDominationPolynomial

/-!
# Tests for the rook domination polynomial

Brute-force counts on the `2 × 2`, `2 × 3` and `3 × 3` boards (by
`decide`), compared with Mertens' formulas: the right-hand sides of
Theorems 1 and 2 and Corollary 3 evaluate to the brute-force counts,
Corollary 3 fails at its threshold, Theorem 4 and Corollary 5 give the
brute-force polynomials, and Theorem 4 gives `421` dominating sets of
the `3 × 3` rook graph.
-/

open Polynomial

namespace MathlibExtTest.Combinatorics.SimpleGraph.RookDominationPolynomial

open MathlibExt.Combinatorics.SimpleGraph.RookDominationPolynomial

/-! ### Brute-force counts -/

-- A single rook leaves the opposite cell of the `2 × 2` board
-- undominated; any two rooks dominate it, but only the two diagonals
-- meet every row and every column.
example : rookDominatingCount 2 2 1 = 0 := by decide
example : rookDominatingCount 2 2 2 = 6 := by decide
example : rookCoverCount 2 2 2 = 2 := by decide

-- The `2 × 3` board.
example : rookDominatingCount 2 3 3 = 20 := by decide
example : rookCoverCount 2 3 4 = 12 := by decide

-- The `3 × 3` board: the `6` placements of `3` rooks meeting every row
-- and every column are the permutation matrices.
example : rookDominatingCount 3 3 2 = 0 := by decide
example : rookDominatingCount 3 3 3 = 48 := by decide
example : rookCoverCount 3 3 3 = 6 := by decide

/-! ### Theorems 1 and 2 and Corollary 3 -/

example : (rookDominatingCount 2 3 3 : ℤ) = 20 := by
  rw [rookDominatingCount_eq_choose_sub_sum_rookCoverCount 2 3 3
    (by decide) (by decide)]
  decide

example : (rookCoverCount 2 3 4 : ℤ) = 12 := by
  rw [rookCoverCount_eq_choose_sub_sum_rookCoverCount 2 3 4
    (by decide) (by decide)]
  decide

-- On the `3 × 3` board Corollary 3 needs `2 < k`.
example : (rookDominatingCount 3 3 3 : ℤ) = 48 := by
  rw [rookDominatingCount_eq_choose_sub_mul_choose 3 3 3
    (by decide) (by decide) (by decide)]
  decide

-- At the threshold `k = 2` the high-density formula fails.
example : (rookDominatingCount 3 3 2 : ℤ) ≠
    ((3 * 3).choose 2 : ℤ) -
      (3 : ℤ) * 3 * (((3 - 1) * (3 - 1)).choose 2 : ℤ) := by
  decide

/-! ### Theorem 4 and Corollary 5 -/

-- From the definition and the brute-force counts.
example : rookDominationPolynomial 2 2 = 6 * X ^ 2 + 4 * X ^ 3 + X ^ 4 := by
  have h0 : rookDominatingCount 2 2 0 = 0 := by decide
  have h1 : rookDominatingCount 2 2 1 = 0 := by decide
  have h2 : rookDominatingCount 2 2 2 = 6 := by decide
  have h3 : rookDominatingCount 2 2 3 = 4 := by decide
  have h4 : rookDominatingCount 2 2 4 = 1 := by decide
  simp only [rookDominationPolynomial, Nat.reduceMul, Nat.reduceAdd,
    Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, map_zero, map_one,
    map_ofNat]
  ring

-- From Theorem 4.
example : rookDominationPolynomial 2 2 = 6 * X ^ 2 + 4 * X ^ 3 + X ^ 4 := by
  rw [rookDominationPolynomial_eq 2 2 (by decide) (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    Nat.cast_ofNat, map_one, map_ofNat]
  ring

-- From Corollary 5; the brute-force counts are `9, 20, 15, 6, 1`.
example : rookDominationPolynomial 2 3 =
    9 * X ^ 2 + 20 * X ^ 3 + 15 * X ^ 4 + 6 * X ^ 5 + X ^ 6 := by
  have h32 : Nat.choose 3 2 = 3 := by decide
  rw [rookDominationPolynomial_eq_symmetric 2 3 (by decide) (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, h32,
    Nat.cast_one, Nat.cast_ofNat, map_one, map_ofNat, map_mul]
  ring

-- Theorem 4 gives the number of dominating sets of the `3 × 3` rook
-- graph.
example : (rookDominationPolynomial 3 3).eval 1 = 421 := by
  have h32 : Nat.choose 3 2 = 3 := by decide
  rw [rookDominationPolynomial_eq 3 3 (by decide) (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, eval_zero,
    eval_sub, eval_add, eval_mul, eval_pow, eval_neg, eval_one, eval_X,
    eval_C, Nat.choose_zero_right, Nat.choose_one_right, h32]
  norm_num

-- The generating polynomial of the cover counts on the `2 × 2` board.
example : ∑ k ∈ Finset.range (2 * 2 + 1),
    C (rookCoverCount 2 2 k : ℤ) * X ^ k =
      2 * X ^ 2 + 4 * X ^ 3 + X ^ 4 := by
  rw [sum_rookCoverCount_mul_X_pow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self,
    Nat.cast_one, Nat.cast_ofNat, map_one, map_ofNat, map_mul]
  ring

#print axioms rookDominatingCount_eq_choose_sub_sum_rookCoverCount
#print axioms rookCoverCount_eq_choose_sub_sum_rookCoverCount
#print axioms rookDominatingCount_eq_choose_sub_mul_choose
#print axioms rookDominationPolynomial_eq
#print axioms rookDominationPolynomial_eq_symmetric
#print axioms sum_rookCoverCount_mul_X_pow
#print axioms card_powersetCard_filter_image_mem

end MathlibExtTest.Combinatorics.SimpleGraph.RookDominationPolynomial
