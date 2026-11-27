/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimitiveLambdaRoots
import Mathlib.Tactic.NormNum

open ArithmeticFunction MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted

example : carmichael 6 = 2 := by
  rw [show 6 = 2 * 3 by decide, carmichael_mul_eq_lcm 2 3 (by decide) (by decide) (by decide),
    carmichael_two, carmichael_of_prime Nat.prime_three]
  decide

example : carmichael 35 = 12 := by
  rw [show 35 = 5 * 7 by decide, carmichael_mul_eq_lcm 5 7 (by decide) (by decide) (by decide),
    carmichael_of_prime (by decide : Nat.Prime 5), carmichael_of_prime (by decide : Nat.Prime 7)]
  decide

example : lambdaH 2 8 = 3 / 4 := by
  have h₈ : carmichael 8 = 2 := carmichael_two_pow_of_ne_two (n := 3) (by decide)
  have hΔ : lambdaDelta 2 8 = 2 := by
    rw [lambdaDelta, h₈, show 8 = 2 ^ 3 by decide, Nat.prime_two.factorization_pow,
      Nat.prime_two.factorization, Nat.primeFactors_prime_pow (by decide : 3 ≠ 0) Nat.prime_two]
    simp
  norm_num [lambdaH, hΔ]

example : primitiveLambdaRootCount 2 = 1 := by
  have h (a : (ZMod 2)ˣ) : orderOf a = carmichael 2 := by
    rw [Subsingleton.elim a 1, orderOf_one, carmichael_two]
  simp [primitiveLambdaRootCount, h]
