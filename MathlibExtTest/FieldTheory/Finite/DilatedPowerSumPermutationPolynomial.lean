/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Finite.DilatedPowerSumPermutationPolynomial

open MetaMathlibExt Polynomial

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The exponent 3 is not divisible by 5 - 1.
example : Polynomial.IsPermutationPolynomial
    (∑ n ∈ Finset.Icc 1 21, C (((3 * n : ℕ) : ZMod 5) ^ 3) * X ^ (3 * n)) :=
  isPermutationPolynomial_sum_mul_pow_mul_X_pow_mul (p := 5) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))

-- The exponent 2 is divisible by 3 - 1, but 3² divides 19 - 1.
example : Polynomial.IsPermutationPolynomial
    (∑ n ∈ Finset.Icc 1 19, C (((5 * n : ℕ) : ZMod 3) ^ 2) * X ^ (5 * n)) :=
  isPermutationPolynomial_sum_mul_pow_mul_X_pow_mul (p := 3) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))

example :
    (∑ n ∈ Finset.Icc 1 21, C (((3 * n : ℕ) : ZMod 5) ^ 3) * X ^ (3 * n)).eval 2 = 1 := by
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  decide
