/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectIsDeficientFPerfectTwoPowMulPrimeImp

namespace MathlibExtTest.NumberTheory.FkPerfectIsDeficientFPerfectTwoPowMulPrimeImp

open MathlibExt.NumberTheory.FkPerfectWanted

-- `6 = 2 ^ 1 * 3` is deficient `F`-perfect with divisor `d = 2`.
example : IsDeficientFPerfect 6 := by
  unfold IsDeficientFPerfect IsKLDeficientPerfect KLDeficientPerfectWith
  exact ⟨2, by decide, by decide, by decide⟩

-- Any deficient `F`-perfect number of the form `2 ^ a * 3` has exponent one.
example (a : ℕ) (h : IsDeficientFPerfect (2 ^ a * 3)) : a = 1 :=
  (isDeficientFPerfect_two_pow_mul_prime_imp 3 a (by decide) h).2

-- `12 = 2 ^ 2 * 3` is not deficient `F`-perfect: the theorem forces `a = 1`.
example : ¬ IsDeficientFPerfect 12 := by
  intro h
  have hcon := isDeficientFPerfect_two_pow_mul_prime_imp 3 2 (by decide) h
  exact absurd hcon.2 (by decide)

-- `10 = 2 ^ 1 * 5` is not deficient `F`-perfect: the theorem forces `p = 3`.
example : ¬ IsDeficientFPerfect 10 := by
  intro h
  have hcon := isDeficientFPerfect_two_pow_mul_prime_imp 5 1 (by decide) h
  exact absurd hcon.1 (by decide)

end MathlibExtTest.NumberTheory.FkPerfectIsDeficientFPerfectTwoPowMulPrimeImp
