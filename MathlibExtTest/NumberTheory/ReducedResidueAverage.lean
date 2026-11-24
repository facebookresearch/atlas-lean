/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResidueAverage
import Mathlib.RingTheory.Radical.NatInt

open UniqueFactorizationMonoid MetaMathlibExt

-- Modulo 12 the largest prime factor minus one equals the radical quotient.
example : (1 / (12 : ℚ)) * ∑ m ∈ Finset.range 12, (longestAPLength m 12 : ℚ) = 2 := by
  have hr : radical 12 = 6 := by rw [Nat.radical_eq_prod_primeFactors]; decide +kernel
  calc
    _ = (12 : ℚ) / radical (12 : ℕ) := average_longestAPLength_of_not_squarefree (n := 12)
      (by decide) (by decide +kernel) (by rw [hr]; decide +kernel)
    _ = 2 := by rw [hr]; norm_num

-- An odd prime power gives strict inequality in the prime-factor hypothesis.
example : (1 / (27 : ℚ)) * ∑ m ∈ Finset.range 27, (longestAPLength m 27 : ℚ) = 9 := by
  have hr : radical 27 = 3 := by rw [Nat.radical_eq_prod_primeFactors]; decide +kernel
  calc
    _ = (27 : ℚ) / radical (27 : ℕ) := average_longestAPLength_of_not_squarefree (n := 27)
      (by decide) (by decide +kernel) (by rw [hr]; decide +kernel)
    _ = 9 := by rw [hr]; norm_num
