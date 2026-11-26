/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Finite.ShiftedPowerSumPermutationPolynomial

namespace MetaMathlibExt.ShiftedPowerSumPermutationPolynomialTest

open Finset Polynomial

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance factPrimeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

-- The exponent is not divisible by 4, and the shift induces the cube map.
example : (∑ n ∈ Icc (1 : ℕ) 21, C ((n : ZMod 5) ^ 1) * X ^ (n + 2)).IsPermutationPolynomial :=
  isPermutationPolynomial_sum_pow_mul_X_pow_add (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide))

-- The exponent is divisible by 2, and the second branch applies because 9 divides 18.
example : (∑ n ∈ Icc (1 : ℕ) 19, C ((n : ZMod 3) ^ 2) * X ^ (n + 2)).IsPermutationPolynomial :=
  isPermutationPolynomial_sum_pow_mul_X_pow_add (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inr (by decide))

end MetaMathlibExt.ShiftedPowerSumPermutationPolynomialTest
