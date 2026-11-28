/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.Partition.MercaSquareSum

open MetaMathlibExt

-- At `n = 0`, there is no square shift and the residue-zero weight vanishes.
example : (sumDistinctPartsModEq 1 0 0 : ℤ) = 0 := by
  simpa using sumDistinctPartsModEq_square_eq_evenOdd 1 0 0 (by decide)

-- At `n = 2`, the ordinary square shift is 1; the single partition of the gap has odd length.
example : (sumDistinctPartsModEq 2 1 2 : ℤ) - 2 * sumDistinctPartsModEq 2 1 1 = -1 := by
  have h := sumDistinctPartsModEq_square_eq_evenOdd 2 1 2 (by decide)
  rw [show (Finset.Icc 1 2).filter (fun k => k ^ 2 ≤ 2) = {1} by decide,
    show (Finset.range 3).filter (fun j => 2 * j + 1 ≤ 2) = {0} by decide] at h
  norm_num [Nat.Partition.partition_one_parts] at h
  linarith

-- At `n = 5`, the positive shift by `2²` contributes exactly 2.
example : (sumDistinctPartsModEq 4 1 5 : ℤ) - 2 * sumDistinctPartsModEq 4 1 4 + 2 =
    (∑ μ : Nat.Partition 4, (-1 : ℤ) ^ μ.parts.card) + 5 := by
  have h := sumDistinctPartsModEq_square_eq_evenOdd 4 1 5 (by decide)
  have h₁ : sumDistinctPartsModEq 4 1 1 = 1 := by
    norm_num [sumDistinctPartsModEq, Finset.filter_singleton]
  rw [show (Finset.Icc 1 5).filter (fun k => k ^ 2 ≤ 5) = {1, 2} by decide,
    show (Finset.range 6).filter (fun j => 4 * j + 1 ≤ 5) = {0, 1} by decide] at h
  norm_num [h₁, Nat.Partition.partition_zero_parts] at h
  linarith
