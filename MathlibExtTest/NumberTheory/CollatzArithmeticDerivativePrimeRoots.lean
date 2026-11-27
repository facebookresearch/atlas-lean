/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.CollatzArithmeticDerivativePrimeRoots

open MetaMathlibExt

-- The first compatible pair in Bradshaw's Table 1, with the larger root first.
example : collatzAccelerated (71 * 1609) = 491 * 349 ∧
    arithmeticDerivative (collatzAccelerated (71 * 1609)) =
      collatzAccelerated (arithmeticDerivative (71 * 1609)) := by
  obtain ⟨hp, hq, hs, hr, _, _⟩ := isCompatibleSemiprimePair_71_1609
  exact collatzAccelerated_mul_eq_and_comm_of_roots_prime 71 1609 491 349 284
    hp hq hr hs (by norm_num) (by norm_num) (by norm_num)

-- The next pair in Table 1 gives the common value 1050, even with the input primes swapped.
example : collatzAccelerated (2029 * 71) = 769 * 281 ∧
    arithmeticDerivative (collatzAccelerated (2029 * 71)) = 1050 ∧
    collatzAccelerated (arithmeticDerivative (2029 * 71)) = 1050 := by
  have hr : Nat.Prime 769 := by norm_num
  have hs : Nat.Prime 281 := by norm_num
  obtain ⟨hC, hcomm⟩ := collatzAccelerated_mul_eq_and_comm_of_roots_prime 2029 71 769 281 976
    (by norm_num) (by norm_num) hr hs (by norm_num) (by norm_num) (by norm_num)
  have hD : arithmeticDerivative (collatzAccelerated (2029 * 71)) = 1050 := by
    rw [hC, arithmeticDerivative_mul, arithmeticDerivative_prime hr, arithmeticDerivative_prime hs]
  exact ⟨hC, hD, hcomm.symm.trans hD⟩
