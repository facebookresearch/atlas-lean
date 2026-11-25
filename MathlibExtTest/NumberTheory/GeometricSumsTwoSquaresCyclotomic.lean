/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeometricSumsTwoSquaresCyclotomic

open Polynomial
open MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

-- For `p = 3`, the alternating polynomials are `X ^ 2 - 1` and `X`.
example : phi4pX1 3 = X ^ 2 - 1 := by
  ext n
  simp [phi4pX1, Finset.sum_range_succ]
  omega

example : phi4pY1 3 = X := by
  ext n
  simp [phi4pY1]

-- For `p = 3` and `k = 2`, the identity at `x = 2` reads
-- `Φ₃₆(2) = 63 ^ 2 + 8 ^ 2 = 4033`, exercising the composition with `x ^ 3`.
example : (Polynomial.cyclotomic (4 * 3 ^ 2) ℤ).eval 2 = 4033 := by
  have h := cyclotomicFourMulPow_eq_sq_add_sq 3 2 Nat.prime_three (by norm_num) (by norm_num)
  rw [h]
  simp [phi4pX1, phi4pY1, Finset.sum_range_succ]

-- For `p = 5` and `k = 1`, the identity at `x = 2` reads
-- `Φ₂₀(2) = 13 ^ 2 + 6 ^ 2 = 205`.
example : (Polynomial.cyclotomic (4 * 5 ^ 1) ℤ).eval 2 = 205 := by
  have h := cyclotomicFourMulPow_eq_sq_add_sq 5 1 Nat.prime_five (by norm_num) (by norm_num)
  rw [h]
  simp [phi4pX1, phi4pY1, Finset.sum_range_succ]
