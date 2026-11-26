/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FunctionFieldMultiplicityIteratedDerivSubIsBigOOfUniformApprox
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.FunctionFieldMultiplicityIteratedDerivSubIsBigOOfUniformApprox` -/

namespace MathlibExtTest.NumberTheory.FunctionFieldMultiplicityIteratedDerivSubIsBigOOfUniformApprox

open Filter MetaMathlibExt

-- With `f = 1` and `Gₙ(z) = n ^ (z - 1)` (and `G₀ = 0`), the approximation is exact, so the
-- first derivatives at `1` differ by `O(n ^ (1 / 2 - 1))`.
example : (fun n : ℕ => iteratedDeriv 1
      (fun z : ℂ => if n = 0 then 0 else (n : ℂ) ^ (z - 1)) 1 -
      iteratedDeriv 1 (fun z : ℂ => 1 * (n : ℂ) ^ (z - 1)) 1) =O[atTop]
    (fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - 1)) := by
  have hG : ∀ n : ℕ, AnalyticOnNhd ℂ
      (fun z : ℂ => if n = 0 then (0 : ℂ) else (n : ℂ) ^ (z - 1))
      (Metric.ball 1 1) := by
    intro n
    by_cases hn : n = 0
    · have e : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (Metric.ball 1 1) :=
        analyticOnNhd_const
      simpa [hn] using e
    · have e : AnalyticOnNhd ℂ (fun z : ℂ => (n : ℂ) ^ (z - 1)) (Metric.ball 1 1) :=
        AnalyticOnNhd.cpow analyticOnNhd_const
          (AnalyticOnNhd.sub analyticOnNhd_id analyticOnNhd_const)
          (fun z _ => Complex.natCast_mem_slitPlane.2 hn)
      simpa [hn] using e
  have hbound : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Metric.ball (1 : ℂ) 1,
      ‖(if n = 0 then (0 : ℂ) else (n : ℂ) ^ (z - 1)) - 1 * (n : ℂ) ^ (z - 1)‖
        ≤ C * (n : ℝ) ^ (z.re - 2) := by
    refine ⟨0, fun n hn z _ => ?_⟩
    have hn0 : n ≠ 0 := by omega
    simp [hn0]
  exact iteratedDeriv_sub_isBigO_of_uniform_approx _ (fun _ => 1) 1 zero_lt_one hG
    analyticOnNhd_const hbound 1 (1 / 2) (by norm_num)

-- At `k = 0` the iterated derivatives evaluate to the function values.
example (G : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hG : ∀ n, AnalyticOnNhd ℂ (G n) (Metric.ball 1 r))
    (hf : AnalyticOnNhd ℂ f (Metric.ball 1 r))
    (hbound : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Metric.ball (1 : ℂ) r,
      ‖G n z - f z * (n : ℂ) ^ (z - 1)‖ ≤ C * (n : ℝ) ^ (z.re - 2))
    (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => G n 1 - f 1 * (n : ℂ) ^ ((1 : ℂ) - 1)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (ε - 1)) := by
  have h := iteratedDeriv_sub_isBigO_of_uniform_approx G f r hr hG hf hbound 0 ε hε
  simpa [iteratedDeriv_zero] using h

end MathlibExtTest.NumberTheory.FunctionFieldMultiplicityIteratedDerivSubIsBigOOfUniformApprox
