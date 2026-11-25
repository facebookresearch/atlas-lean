/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.DigitSumArithSqPartialSum
import Mathlib.Tactic.NormNum

/-! # Tests for partial sums of the second digit-sum convolution -/

open MetaMathlibExt
open Filter Asymptotics Real

-- In base two, the Dirichlet square of the digit sum takes the value 3 at 4.
example : (digitSumArith 2 ^ 2) 4 = 3 := by
  rw [digitSumArith_sq_apply]
  decide

-- The partial sum of the Dirichlet square over 1 ≤ n ≤ 3 in base two is 7.
example : ∑ n ∈ Finset.Icc 1 3, ((digitSumArith 2 ^ 2) n : ℝ) = 7 := by
  rw [← Nat.cast_sum]
  norm_num [show (∑ n ∈ Finset.Icc 1 3, (digitSumArith 2 ^ 2) n) = 7 from by decide]

-- The asymptotic formula specializes to base three.
example : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith 3 ^ 2) n : ℝ) -
    ((3 : ℝ) - 1) ^ 2 * x * log x ^ 3 / (24 * log 3 ^ 2)) =O[atTop]
      (fun x => x * log x ^ 2) :=
  digitSumArith_sq_partialSum_isBigO 3 (by norm_num)
