/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.SolowGoldenRule
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

open MathlibExt.Economics.Macro.SolowGoldenRule
/-!
# Tests for the golden-rule condition

Reduction of the unconstrained first-order condition to `deriv f k = delta` when `n = g = 0`,
its concrete quadratic instance, the objective value `2401/100` at the example maximum, and a
concrete instance of `goldenRule_condition` whose hypotheses all hold: the quadratic example at
`k = 49/10` is a feasible steady state with saving rate `98/2499`, and every capital stock in
`(1, 9)` is a feasible steady state.
-/

@[expose] public section

open scoped Topology

namespace MathlibExtTest.Economics.Macro.SolowGoldenRule

/-- Reduction of the unconstrained first-order condition to `deriv f k = δ` when
`n = g = 0`. -/
theorem goldenRule_n_g_zero {f : ℝ → ℝ} {δ k : ℝ}
    (hdiff : DifferentiableAt ℝ f k)
    (hmax : IsLocalMax (goldenConsumption f δ 0 0) k) :
    deriv f k = δ := by
  have h := deriv_eq_breakEven_of_isLocalMax hdiff hmax
  simpa using h

/-- Concrete `n = g = 0` instance: `f(k) = -k ^ 2 + 10 * k`, `δ = 1 / 5`;
the objective's maximum is at `k = 49 / 10` with `deriv f (49 / 10) = 1 / 5`. -/
theorem goldenRule_example_n_g_zero :
    IsLocalMax (goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 5) 0 0)
        (49 / 10) ∧
      deriv (fun k : ℝ => -k ^ 2 + 10 * k) (49 / 10) = 1 / 5 := by
  have hpow : HasDerivAt (fun k : ℝ => k ^ 2) (2 * (49 / 10)) (49 / 10) := by
    simpa using hasDerivAt_pow 2 (49 / 10 : ℝ)
  have hlin : HasDerivAt (fun k : ℝ => 10 * k) 10 (49 / 10) := by
    simpa using (hasDerivAt_id (49 / 10 : ℝ)).const_mul 10
  have hdiff : DifferentiableAt ℝ (fun k : ℝ => -k ^ 2 + 10 * k) (49 / 10) :=
    (hpow.neg.add hlin).differentiableAt
  have hmax : IsMaxOn
      (goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 5) 0 0)
      Set.univ (49 / 10) := by
    intro k _
    show goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 5) 0 0 k ≤
      goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 5) 0 0 (49 / 10)
    have hdiff2 : goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 5) 0 0
          (49 / 10)
        - goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 5) 0 0 k
        = (k - 49 / 10) ^ 2 := by
      simp only [goldenConsumption]
      ring
    have hsq : 0 ≤ (k - 49 / 10) ^ 2 := sq_nonneg _
    linarith [hdiff2, hsq]
  have hlocal := hmax.isLocalMax (isOpen_univ.mem_nhds (Set.mem_univ _))
  have hcond := goldenRule_n_g_zero hdiff hlocal
  exact ⟨hlocal, hcond⟩

/-- The objective at the example maximum equals `2401 / 100`. -/
theorem goldenConsumption_example_value :
    goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 10) (1 / 10) 0 (49 / 10)
      = 2401 / 100 := by
  unfold goldenConsumption
  norm_num

/-- The example point `k = 49 / 10` is a feasible steady state: capital and output
`2499 / 100` are nonnegative, and the saving rate `98 / 2499` lies in `[0, 1]` and sustains
it. -/
theorem goldenRule_example_feasible :
    IsFeasibleSteadyState (fun k : ℝ => -k ^ 2 + 10 * k) (98 / 2499) (1 / 10) (1 / 10) 0
      (49 / 10) := by
  refine ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num⟩, ?_⟩
  unfold IsSteadyState
  norm_num

/-- `goldenRule_condition` applies to the quadratic example: every capital stock `x ∈ (1, 9)`
is a feasible steady state (positive capital and output) with saving rate
`1 / (5 * (10 - x))`, steady-state consumption is maximal at `k = 49 / 10`, and the condition
gives `deriv f (49 / 10) = 1 / 5`. -/
theorem goldenRule_feasible_example :
    deriv (fun k : ℝ => -k ^ 2 + 10 * k) (49 / 10) = 1 / 5 := by
  have hpow : HasDerivAt (fun k : ℝ => k ^ 2) (2 * (49 / 10)) (49 / 10) := by
    simpa using hasDerivAt_pow 2 (49 / 10 : ℝ)
  have hlin : HasDerivAt (fun k : ℝ => 10 * k) 10 (49 / 10) := by
    simpa using (hasDerivAt_id (49 / 10 : ℝ)).const_mul 10
  have hdiff : DifferentiableAt ℝ (fun k : ℝ => -k ^ 2 + 10 * k) (49 / 10) :=
    (hpow.neg.add hlin).differentiableAt
  have hint : ∀ᶠ x in 𝓝 (49 / 10 : ℝ), ∃ s, IsFeasibleSteadyState
      (fun k : ℝ => -k ^ 2 + 10 * k) s (1 / 10) (1 / 10) 0 x := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (1 : ℝ) < 49 / 10)
      (by norm_num : (49 / 10 : ℝ) < 9)] with x hx
    obtain ⟨hx1, hx9⟩ := hx
    have hpos : 0 < 5 * (10 - x) := by linarith
    refine ⟨1 / (5 * (10 - x)), ⟨by linarith, by nlinarith, ⟨by positivity, ?_⟩, ?_⟩⟩
    · rw [div_le_one hpos]
      linarith
    · unfold IsSteadyState
      have hne : (10 : ℝ) - x ≠ 0 := (by linarith : (0 : ℝ) < 10 - x).ne'
      field_simp
      ring
  have hmax : ∀ᶠ x in 𝓝 (49 / 10 : ℝ), ∀ s, IsFeasibleSteadyState
      (fun k : ℝ => -k ^ 2 + 10 * k) s (1 / 10) (1 / 10) 0 x →
      (1 - s) * (-x ^ 2 + 10 * x) ≤ (1 - 98 / 2499) * (-(49 / 10) ^ 2 + 10 * (49 / 10)) := by
    refine Filter.Eventually.of_forall fun x s hs => ?_
    have h1 := consumption_eq_goldenConsumption hs.steady
    have h2 := consumption_eq_goldenConsumption goldenRule_example_feasible.steady
    simp only [goldenConsumption] at h1 h2
    nlinarith [sq_nonneg (x - 49 / 10)]
  have h := goldenRule_condition hdiff goldenRule_example_feasible hint hmax
  rw [h]
  norm_num

end MathlibExtTest.Economics.Macro.SolowGoldenRule
