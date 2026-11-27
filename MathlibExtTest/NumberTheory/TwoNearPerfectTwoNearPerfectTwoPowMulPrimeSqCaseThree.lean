/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSqCaseThree

/-!
# Tests for two-near perfect numbers with omitted divisors `1` and `2^b p^2`

Apply the classification to `36` and exclude the prime `5`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 3.
-/

namespace MathlibExtTest.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSqCaseThree

example : 2 ^ 2 * 3 ^ 2 = 36 ∧ 2 ^ 1 * 3 ^ 2 = 18 := by
  exact MetaMathlibExt.two_near_perfect_two_pow_mul_prime_sq_case_three
    (k := 2) (p := 3) (b := 1) (by decide) (by decide) (by decide) (by decide) (by decide)

example {k b : ℕ} (hb : 1 ≤ b) (hbk : b ≤ k) :
    ArithmeticFunction.sigma 1 (2 ^ k * 5 ^ 2) ≠
      2 * (2 ^ k * 5 ^ 2) + 1 + 2 ^ b * 5 ^ 2 := by
  intro hσ
  have h := (MetaMathlibExt.two_near_perfect_two_pow_mul_prime_sq_case_three
    (p := 5) (by decide) (by decide) hb hbk hσ).1
  omega

end MathlibExtTest.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSqCaseThree
