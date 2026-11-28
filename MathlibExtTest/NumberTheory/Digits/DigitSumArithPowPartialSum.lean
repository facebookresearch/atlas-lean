/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.DigitSumArithPowPartialSum
import Mathlib.Tactic.NormNum

/-! # Tests for partial sums of iterated digit-sum convolutions -/

open MetaMathlibExt Filter Asymptotics Real

private theorem floor_seven_halves : ⌊(7 / 2 : ℝ)⌋₊ = 3 :=
  (Nat.floor_eq_iff (by norm_num)).2 (by norm_num)

-- The binary square and cube give different sums; the cutoff is not an integer.
example : ∑ n ∈ Finset.Icc 1 ⌊(7 / 2 : ℝ)⌋₊, ((digitSumArith 2 ^ 2) n : ℝ) = 7 := by
  rw [floor_seven_halves, ← Nat.cast_sum]
  exact_mod_cast (show ∑ n ∈ Finset.Icc 1 3, (digitSumArith 2 ^ 2) n = 7 by decide)

example : ∑ n ∈ Finset.Icc 1 ⌊(7 / 2 : ℝ)⌋₊, ((digitSumArith 2 ^ 3) n : ℝ) = 10 := by
  rw [floor_seven_halves, ← Nat.cast_sum]
  exact_mod_cast (show ∑ n ∈ Finset.Icc 1 3, (digitSumArith 2 ^ 3) n = 10 by decide)

-- The first recurrence step gives the binomial factor 1/20, in addition to 1/(2 log 2).
example : digitConvolutionCoeff 2 3 = digitConvolutionCoeff 2 2 * (1 / (2 * log 2)) * (1 / 20) := by
  rw [digitConvolutionCoeff_succ 2 (by decide : 2 ≤ 2)]
  norm_num [Finset.sum_range_succ, Nat.choose]

-- API check: the cube has log powers 5 and 4 in the main term and error, respectively.
example : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith 2 ^ 3) n : ℝ) -
    digitConvolutionCoeff 2 3 * x * log x ^ 5) =O[atTop] (fun x => x * log x ^ 4) :=
  digitSumArith_pow_partialSum_isBigO 2 (by decide) 3 (by decide)
