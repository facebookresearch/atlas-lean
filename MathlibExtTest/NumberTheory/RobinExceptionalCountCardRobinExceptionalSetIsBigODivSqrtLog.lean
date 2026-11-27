/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Asymptotics.Defs
import MathlibExt.NumberTheory.RobinExceptionalCountCardRobinExceptionalSetIsBigODivSqrtLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

namespace MathlibExtTest.NumberTheory.RobinExceptionalCountCardRobinExceptionalSetIsBigODivSqrtLog

/-- The exceptional set up to `5040` is empty. -/
example : MetaMathlibExt.robinExceptionalSet 5040 = ∅ := by
  simp [MetaMathlibExt.robinExceptionalSet]

/-- Membership in the exceptional set unfolds to the defining bounds. -/
example (x : ℝ) (n : ℕ) :
    n ∈ MetaMathlibExt.robinExceptionalSet x ↔
      5040 < n ∧ n ≤ ⌊x⌋₊ ∧
        Real.exp Real.eulerMascheroniConstant * (n : ℝ)
          * Real.log (Real.log (n : ℝ)) ≤ (ArithmeticFunction.sigma 1 n : ℝ) := by
  simp only [MetaMathlibExt.robinExceptionalSet, Finset.mem_filter, Finset.mem_Ioc,
    and_assoc]

/-- The counting function is also `O(x)`. -/
example : (fun x : ℝ => ((MetaMathlibExt.robinExceptionalSet x).card : ℝ)) =O[atTop]
    fun x : ℝ => x :=
  MetaMathlibExt.card_robinExceptionalSet_isBigO_div_sqrt_log.trans (by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
    have h1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hx
      rwa [Real.log_exp] at h
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (Real.log x) := by
      have h := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at h
    have hdiv : x / Real.sqrt (Real.log x) ≤ x := by
      have hsqrtpos : (0 : ℝ) < Real.sqrt (Real.log x) :=
        lt_of_lt_of_le zero_lt_one hsqrt1
      exact div_le_self hx0.le hsqrt1
    have hgnn : (0 : ℝ) ≤ x / Real.sqrt (Real.log x) :=
      div_nonneg hx0.le (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgnn, abs_of_nonneg hx0.le]
    simpa [one_mul] using hdiv)

end MathlibExtTest.NumberTheory.RobinExceptionalCountCardRobinExceptionalSetIsBigODivSqrtLog
