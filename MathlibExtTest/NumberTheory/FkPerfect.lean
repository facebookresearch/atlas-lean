/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfect

namespace MathlibExtTest.NumberTheory.FkPerfect

-- `18 = 2 ^ 1 * 3 ^ 2` is not near `F`-perfect.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect 18 := by
  simpa using MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime_pow
    3 1 2 (by decide) (by decide)

-- `2500 = 2 ^ 2 * 5 ^ 4` is not near `F`-perfect.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect 2500 := by
  simpa using MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime_pow
    5 2 4 (by decide) (by decide)

-- `8 = 2 ^ 3 * 11 ^ 0` is not near `F`-perfect.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect 8 := by
  simpa using MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime_pow
    11 3 0 (by decide) (by decide)

end MathlibExtTest.NumberTheory.FkPerfect
