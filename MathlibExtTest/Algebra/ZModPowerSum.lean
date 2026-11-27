/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.ZModPowerSum

namespace MathlibExt.Algebra.PermutationPolynomialsWanted

-- For p = 2, every positive exponent is divisible by p - 1 = 1.
example : (∑ a : ZMod 2, a ^ 5) = -1 := by
  simpa using sum_zmod_pow_eq_ite 2 5 Nat.prime_two (by decide)

-- The exponent is a multiple of p - 1.
example : (∑ a : ZMod 5, a ^ 8) = -1 := by
  simpa using sum_zmod_pow_eq_ite 5 8 (by decide) (by decide)

-- The exponent is not a multiple of p - 1.
example : (∑ a : ZMod 5, a ^ 6) = 0 := by
  simpa using sum_zmod_pow_eq_ite 5 6 (by decide) (by decide)

end MathlibExt.Algebra.PermutationPolynomialsWanted
