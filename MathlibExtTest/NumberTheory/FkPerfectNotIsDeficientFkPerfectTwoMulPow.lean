/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsDeficientFkPerfectTwoMulPow

/-!
# Tests for deficient `F_k`-perfect numbers of the form `2 * p ^ a`

These examples exclude `2` and `6` for `k = 3`, and exclude twice every power
of `3` for every `k > 2`.
-/

namespace MathlibExtTest.NumberTheory.FkPerfectNotIsDeficientFkPerfectTwoMulPow

open MathlibExt.NumberTheory.FkPerfectWanted

example : ¬ IsDeficientFkPerfect 3 2 := by
  simpa only [pow_zero, mul_one] using
    not_isDeficientFkPerfect_two_mul_pow 3 3 0 (by decide) (by decide) (by decide)

example : ¬ IsDeficientFkPerfect 3 6 := by
  simpa only [pow_one] using
    not_isDeficientFkPerfect_two_mul_pow 3 3 1 (by decide) (by decide) (by decide)

example (k a : ℕ) (hk : 2 < k) : ¬ IsDeficientFkPerfect k (2 * 3 ^ a) :=
  not_isDeficientFkPerfect_two_mul_pow k 3 a hk (by decide) (by decide)

end MathlibExtTest.NumberTheory.FkPerfectNotIsDeficientFkPerfectTwoMulPow
