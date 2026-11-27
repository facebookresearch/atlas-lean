/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsNearFPerfectTwoMulPrimePow

namespace MathlibExtTest.NumberTheory.FkPerfectNotIsNearFPerfectTwoMulPrimePow

open MathlibExt.NumberTheory.FkPerfectWanted

-- An odd prime base at a positive exponent.
example : ¬ IsNearFPerfect (2 * 3 ^ 4) :=
  not_isNearFPerfect_two_mul_prime_pow 3 4 (by decide)

-- The prime two, where `2 * 2 ^ a` is itself a power of two.
example : ¬ IsNearFPerfect (2 * 2 ^ 6) :=
  not_isNearFPerfect_two_mul_prime_pow 2 6 (by decide)

-- `6` is deficient-`F`-perfect but not near-`F`-perfect.
example : ¬ IsNearFPerfect 6 := by
  simpa using not_isNearFPerfect_two_mul_prime_pow 3 1 (by decide)

-- No divisor can witness the equation for `2 * 5 ^ a`.
example (a d : ℕ) : ¬ KLNearPerfectWith 2 3 (2 * 5 ^ a) d := fun h =>
  not_isNearFPerfect_two_mul_prime_pow 5 a (by decide) ⟨d, h⟩

end MathlibExtTest.NumberTheory.FkPerfectNotIsNearFPerfectTwoMulPrimePow
