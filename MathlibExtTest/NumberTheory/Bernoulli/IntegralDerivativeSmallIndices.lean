/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.IntegralDerivativeSmallIndices
import MathlibExt.NumberTheory.BernoulliDerivativeDenominatorBernoulliDerivativeIntegralIff

open MetaMathlibExt

-- Compute the full coprime part directly, without using the small-prime sieve.
example :
    ((List.range 100).filter fun n => decide (0 < n ∧ bernoulliDiffDenominatorCoprimePart n = 1)) =
      [1, 2, 4, 6, 10, 12, 28, 30, 36, 60] := by
  decide +kernel

-- Independently check primality for every successor on the list.
example :
    ([1, 2, 4, 6, 10, 12, 28, 30, 36, 60] : List ℕ).all (fun n => decide (n + 1).Prime) = true := by
  decide +kernel

-- Both candidates pass the smaller-prime conditions but fail in base 23.
example : ([2, 3, 5, 7, 11, 13, 17, 19] : List ℕ).all (fun p =>
    decide ((p ∣ 156 ∨ (p.digits 156).sum < p) ∧ (p ∣ 9699690 ∨ (p.digits 9699690).sum < p))) =
      true := by
  decide +kernel

example : (23 : ℕ).Prime ∧ ¬ 23 ∣ 156 ∧ 23 ≤ (Nat.digits 23 156).sum ∧
    ¬ 23 ∣ 9699690 ∧ 23 ≤ (Nat.digits 23 9699690).sum := by
  decide +kernel

-- The cutoff itself is excluded by the base-3 digit sum, without enumerating up to it.
example : (10 ^ 7 : ℕ) ∉ bernoulliIntegralDerivativeIndices 1 := by
  intro h
  have hpart := (bernoulli_derivative_integral_iff (10 ^ 7) (by decide)).1.mp h
  have hd := (prime_dvd_bernoulliDiffDenominatorCoprimePart_iff Nat.prime_three).mpr
    (show ¬ (3 : ℕ) ∣ 10 ^ 7 ∧ 3 ≤ (Nat.digits 3 (10 ^ 7)).sum by decide +kernel)
  rw [hpart] at hd
  exact Nat.prime_three.ne_one (Nat.dvd_one.mp hd)

-- A client of the public theorem at the largest known index.
example : (60 + 1 : ℕ).Prime :=
  bernoulli_integral_derivative_succ_prime_and_large.1 60
    ((bernoulli_derivative_integral_iff 60 (by decide)).1.mpr (by decide +kernel))
