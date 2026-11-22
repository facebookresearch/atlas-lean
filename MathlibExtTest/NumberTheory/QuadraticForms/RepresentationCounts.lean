/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.JacobiTwoSquareCount
public import MathlibExt.NumberTheory.QuadraticForms.SqrtNeg2Count
public import Mathlib.Tactic.NormNum

@[expose] public section

open SumSquares

example :
    (SumSquares.representationNumber 2 5 : ℤ) = 8 := by
  rw [representationNumber_two_jacobi_count 5 (by norm_num)]
  change 4 * SumSquares.divChiSum 5 = 8
  rw [show 5 = 5 ^ 1 by norm_num,
    SumSquares.divChiSum_prime_pow_split (p := 5) (e := 1)
      (by decide) (by decide)]
  norm_num

example :
    (Fintype.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = ((3 : ℕ) : ℤ)} : ℤ) = 4 := by
  rw [x2_add_two_sq_count 3 (by norm_num)]
  change 2 * SumSquares.divChiNeg2Sum 3 = 4
  rw [show 3 = 3 ^ 1 by norm_num,
    SumSquares.divChiNeg2Sum_prime_pow_split (p := 3) (e := 1)
      (by decide) (Or.inr (by decide))]
  norm_num

#print axioms SumSquares.representationNumber_two_jacobi_count
#print axioms SumSquares.x2_add_two_sq_count
