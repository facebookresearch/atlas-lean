/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Prime.Basic
import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibility

open MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

-- At the smallest allowed index, the orbit modulo F₂ is a singleton.
example : pisanoPeriod (Nat.fib 2) = 1 := by
  rw [Nat.fib_two, pisanoPeriod]
  exact Function.minimalPeriod_eq_one_of_subsingleton

-- At n = 4 the bound is attained. The pair modulo F₄ = 3 has not returned after four steps.
example : pisanoPeriod 3 = 8 := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow (k := 2) Nat.prime_two
  · rw [pisanoPeriod, ← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    decide
  · exact pisanoPeriod_fib_dvd_two_mul 4 (by decide) (by decide)
