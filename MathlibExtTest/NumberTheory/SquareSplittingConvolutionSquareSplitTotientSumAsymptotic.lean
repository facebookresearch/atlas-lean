/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitTotientSumAsymptotic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.NormNum

/-! Tests for the square-splitting totient average order and its prime correction series. -/

namespace MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitTotientSumAsymptotic

open Asymptotics Filter MetaMathlibExt

example (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (φ n : ℝ) -
      (∏' p : Nat.Primes,
        (1 - 1 / ((p : ℕ) : ℝ) ^ 2 + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5)) /
        2 * x ^ 2) =O[atTop] fun x => x ^ (5 / 4 : ℝ) := by
  have h := (squareSplitTotient_sum_asymptotic φ hφ).2 (1 / 4) (by norm_num) (by norm_num)
  simpa only [show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num] using h

example (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    Summable (fun p : Nat.Primes =>
      -(1 / ((p : ℕ) : ℝ) ^ 2) + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using (squareSplitTotient_sum_asymptotic φ hφ).1

end MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitTotientSumAsymptotic
