/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.GcdSumMoments

open MetaMathlibExt

-- The first admissible pair is k = 2, m = 3, so the sum includes r = 4.
example : ∑ r ∈ Finset.range 5,
    (-1 : ℤ) ^ r * (Nat.choose 4 r : ℤ) * ((4 : ℤ) - r) ^ 2 = 0 :=
  alternating_choose_two_pow_mul_pow_eq_zero 2 3 (by decide) (by decide)

-- At m = 2 the sum stops at r = 3 and no longer vanishes.
example : ∑ r ∈ Finset.range 4,
    (-1 : ℤ) ^ r * (Nat.choose 4 r : ℤ) * ((3 : ℤ) - r) ^ 2 = -1 := by
  decide
