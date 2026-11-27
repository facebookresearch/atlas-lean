/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsNearFPerfectTwoPowMulPrime
namespace MathlibExtTest.NumberTheory.FkPerfect

example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect (2 ^ 2 * 3) :=
  MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime 3 2 (by decide)

example (a : ℕ) : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect (2 ^ a * 3) :=
  MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime 3 a (by decide)

example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect 6 := by
  have h :=
    MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime 3 1 (by decide)
  simpa using h

-- The prime `2`, which Theorem 10's odd-prime statement does not cover.
example (a : ℕ) : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFPerfect (2 ^ a * 2) :=
  MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFPerfect_two_pow_mul_prime 2 a Nat.prime_two

end MathlibExtTest.NumberTheory.FkPerfect
