/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# An upper bound for the divisor summatory function

For every natural number `N`, the sum of the divisor counts of the positive integers up to `N`
is at most `N * (1 + log N)`. Counting the same divisor pairs by their first factor gives a sum
of floor quotients, which is bounded by `N` times the harmonic sum.

## References

* The Lean proof is extracted from `sum_tau_le` in
  [`MathlibExt.NumberTheory.RobinExceptionalCountCardRobinExceptionalSetIsBigODivSqrtLog`](https://github.com/facebookresearch/atlas-lean/blob/9ab9827017c4c4046fb6582bd187818d74f4da8f/MathlibExt/NumberTheory/RobinExceptionalCountCardRobinExceptionalSetIsBigODivSqrtLog.lean#L93-L114).
* Florian Luca and Patrick Solé, *On Robin’s Inequality*, INTEGERS 25 (2025), Article A8,
  pp. 1–7, proof of Theorem 2 (p. 3), uses the stronger asymptotic divisor-sum estimate. The
  elementary upper bound here suffices for that application.
-/

namespace MetaMathlibExt

open Finset in
/-- The sum of the numbers of positive divisors of `1, …, N` is at most `N * (1 + log N)`. -/
public theorem sum_tau_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ)
      ≤ (N : ℝ) * (1 + Real.log N) := by
  have h : ∑ n ∈ Icc 1 N, n.divisors.card = ∑ d ∈ Icc 1 N, N / d := by
    rw [show Icc 1 N = Ioc 0 N from Icc_add_one_left_eq_Ioc 0 N]
    simpa only [ArithmeticFunction.sigma_zero_apply] using
      ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N
  have hR : ∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) = ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [hR]
  calc
    ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) ≤ ∑ d ∈ Icc 1 N, (N : ℝ) / d :=
      sum_le_sum fun _ _ => Nat.cast_div_le
    _ = (N : ℝ) * ∑ d ∈ Icc 1 N, (1 / (d : ℝ)) := by
      rw [mul_sum]
      exact sum_congr rfl fun d _ => (mul_one_div (N : ℝ) d).symm
    _ ≤ (N : ℝ) * (1 + Real.log N) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
        using harmonic_le_one_add_log N

end MetaMathlibExt
