/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.FisherRate
import Mathlib.Tactic.NormNum

open MathlibExt.Economics.Macro.FisherRate
/-!
# Tests for the exact Fisher rate identity

Large inflation (`r = pi = 1`): exact rate `3`, additive approximation `2`,
error `1`. Zero cross term (`r = 0`): the approximation is exact. An
independently given rate `i = 21/100` at `r = pi = 1/10` satisfies the
relation, with error `1/100`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.FisherRate

/-- Large-inflation case `r = π = 1`: exact nominal rate 3, additive
approximation 2, error 1. -/
theorem fisher_large_inflation :
    fisherNominalRate 1 1 = 3 ∧
      fisherNominalRate 1 1 - (1 + 1) = 1 := by
  refine ⟨by unfold fisherNominalRate; norm_num, by unfold fisherNominalRate; norm_num⟩

/-- Zero cross-term case `r = 0, π = 1/10`: the additive approximation is
exact (error 0). -/
theorem fisher_zero_cross_exact :
    fisherNominalRate 0 (1 / 10) = 1 / 10 ∧
      fisherNominalRate 0 (1 / 10) - (0 + 1 / 10) = 0 := by
  refine ⟨?_, ?_⟩ <;> unfold fisherNominalRate <;> norm_num

/-- An independently given nominal rate `i = 21/100` satisfies the Fisher
relation at `r = π = 1/10`, and its additive-approximation error is the cross
term `1/100`. -/
theorem fisher_relation_given_rate :
    (1 : ℝ) + 21 / 100 = (1 + 1 / 10) * (1 + 1 / 10) ∧
      (21 / 100 : ℝ) - (1 / 10 + 1 / 10) = 1 / 100 := by
  have h : (1 : ℝ) + 21 / 100 = (1 + 1 / 10) * (1 + 1 / 10) := by norm_num
  refine ⟨h, ?_⟩
  rw [fisher_approx_error_of_relation h]
  norm_num
end MathlibExtTest.Economics.Macro.FisherRate
