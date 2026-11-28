/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.MoebiusLiouvilleBounds

/-!
# Tests for summatory bounds of `λ` and convergence of `∑ μ(n) / n^s` on `re s = 1`
-/

@[expose] public section

open Asymptotics Filter ArithmeticFunction

-- `L(8) = ∑_{n ≤ 8} λ(n) = -2` and `L(10) = 0`.
example : ∑ n ∈ Finset.Icc 1 8, liouville n = -2 := by decide +kernel
example : ∑ n ∈ Finset.Icc 1 10, liouville n = 0 := by decide +kernel

example : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((liouville n : ℤ) : ℝ))
      =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) :=
  sum_liouville_isBigO_mul_exp_neg_mul_log_rpow

-- `s = 1`: `∑ μ(n) / n` converges.
example : ∃ L : ℂ, Tendsto
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℂ) / (n : ℂ) ^ (1 : ℂ)) atTop (nhds L) :=
  exists_tendsto_sum_moebius_div_cpow_of_re_eq_one (by norm_num)

example (t : ℝ) : ∃ L : ℂ, Tendsto
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℂ) / (n : ℂ) ^ (1 + t * Complex.I))
      atTop (nhds L) :=
  exists_tendsto_sum_moebius_div_cpow_of_re_eq_one (by simp)
