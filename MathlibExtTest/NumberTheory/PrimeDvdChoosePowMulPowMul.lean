/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeDvdChoosePowMulPowMul

/-!
# Tests for prime divisibility of binomial coefficients with unequal prime powers
-/

namespace MetaMathlibExt

-- Both arguments are divisible by 3, and the coefficient is nonzero.
example : 3 ∣ (18 : ℕ).choose 6 :=
  prime_dvd_choose_pow_mul_pow_mul (a := 2) (b := 2) (r := 2) (s := 1)
    (by decide) (by decide) (by decide) (by decide)

-- At s = 0 the lower argument can exceed the upper one.
example : 3 ∣ (3 : ℕ).choose 4 :=
  prime_dvd_choose_pow_mul_pow_mul (a := 1) (b := 4) (r := 1) (s := 0)
    (by decide) (by decide) (by decide) (by decide)

end MetaMathlibExt
