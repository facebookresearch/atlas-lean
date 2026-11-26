/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimePow

/-! # Tests for `MathlibExt.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimePow` -/

namespace MathlibExtTest.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimePow

open MetaMathlibExt

-- Powers of two: the bound is attained with `p = 2`.
example : absLeastAPLength 8 = 4 :=
  absLeastAPLength_prime_pow (p := 2) (r := 3) (by decide) (by decide) (Or.inl rfl)

-- An odd prime power with `r = 2`.
example : absLeastAPLength 9 = 3 :=
  absLeastAPLength_prime_pow (p := 3) (r := 2) (by decide) (by decide) (Or.inr (by decide))

-- The smallest allowed modulus `2 ^ 1`.
example : absLeastAPLength 2 = 1 :=
  absLeastAPLength_prime_pow (p := 2) (r := 1) (by decide) (by decide) (Or.inl rfl)

end MathlibExtTest.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimePow
