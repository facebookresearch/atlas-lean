/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.MoebiusConvolutionBounds

/-!
# Tests for summatory bounds of `μ * μ` and `μ d`
-/

@[expose] public section

open Asymptotics Filter ArithmeticFunction

-- `(μ * μ)(p) = -2` at a prime, `(μ * μ)(p²) = 1`.
example : (moebius * moebius) 2 = -2 := by decide +kernel
example : (moebius * moebius) 4 = 1 := by decide +kernel

example : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((moebius * moebius) n : ℤ) : ℝ))
      =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) :=
  sum_moebius_mul_moebius_isBigO_mul_exp_neg_mul_log_rpow

example : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) * ((sigma 0 n : ℕ) : ℝ))
      =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) :=
  sum_moebius_mul_sigma_zero_isBigO_mul_exp_neg_mul_log_rpow
