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

open MathlibExt.Economics.Macro.SolowGoldenRule
/-!
# Tests for the golden-rule condition

Reduction to `deriv f k = delta` when `n = g = 0`, its concrete quadratic
instance, and the consumption value `2401/100` at the pinned example maximum.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.SolowGoldenRule

/-- Reduction of the golden-rule condition to `deriv f k = δ` when `n = g = 0`. -/
theorem goldenRule_n_g_zero {f : ℝ → ℝ} {δ k : ℝ}
    (hdiff : DifferentiableAt ℝ f k)
    (hmax : IsLocalMax (goldenConsumption f δ 0 0) k) :
    deriv f k = δ := by
  have h := goldenRule_condition hdiff hmax
  simpa using h

/-- Concrete `n = g = 0` instance: `f(k) = -k ^ 2 + 10 * k`, `δ = 1 / 5`;
the golden point is `k = 49 / 10` with `deriv f (49 / 10) = 1 / 5`. -/
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

/-- Steady-state consumption at the pinned example maximum equals `2401 / 100`. -/
theorem goldenConsumption_example_value :
    goldenConsumption (fun k : ℝ => -k ^ 2 + 10 * k) (1 / 10) (1 / 10) 0 (49 / 10)
      = 2401 / 100 := by
  unfold goldenConsumption
  norm_num
end MathlibExtTest.Economics.Macro.SolowGoldenRule
