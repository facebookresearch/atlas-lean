/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.GovernmentDebtRatio
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for the government debt ratio recurrence

Concrete values `r = 1/20`, `g = 1/50`, `B 0 = 100`, `Y 0 = 100`,
`D 1 = 51/5`: the recurrence holds and both sides evaluate to `96/85`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.GovernmentDebtRatio

open MathlibExt.Economics.Macro.GovernmentDebtRatio

/-- Concrete nominal debt path with `B 0 = 100` and `B 1 = 576/5`. -/
noncomputable def Btest : ℕ → ℝ := fun t => 100 + (76 / 5) * t

/-- Concrete output path growing at `g = 1/50`, with `Y 0 = 100`, `Y 1 = 102`. -/
noncomputable def Ytest : ℕ → ℝ := fun t => 100 * (1 + 1 / 50) ^ t

/-- Concrete primary deficit backed out of the debt law with `r = 1/20`,
so that `D 1 = 51/5`. -/
noncomputable def Dtest : ℕ → ℝ := fun t => Btest t - (1 + 1 / 20) * Btest (t - 1)

theorem test_hg : (1 : ℝ) + 1 / 50 ≠ 0 := by norm_num

theorem test_hY : ∀ t, Ytest t ≠ 0 := by
  intro t
  have h : (0 : ℝ) < Ytest t := by
    simp only [Ytest]
    positivity
  exact ne_of_gt h

theorem test_hYg : ∀ t, Ytest (t + 1) = (1 + 1 / 50) * Ytest t := by
  intro t
  simp only [Ytest, pow_succ]
  ring

theorem test_hB : ∀ t, Btest (t + 1) = (1 + 1 / 20) * Btest t + Dtest (t + 1) := by
  intro t
  simp only [Dtest, Nat.add_sub_cancel]
  ring

/-- The recurrence holds on the concrete values, via `debtRatio_succ`. -/
theorem debtRatio_test_recurrence :
    debtRatio Btest Ytest 1
      = ((1 + 1 / 20) / (1 + 1 / 50)) * debtRatio Btest Ytest 0
        + deficitRatio Dtest Ytest 1 := by
  have h := debtRatio_succ (r := 1 / 20) (g := 1 / 50)
    test_hg test_hY test_hYg test_hB 0
  simpa using h

/-- Left-hand side evaluates to the exact value `96/85`. -/
theorem debtRatio_test_eval : debtRatio Btest Ytest 1 = 96 / 85 := by
  unfold debtRatio Btest Ytest
  simp
  norm_num

/-- Right-hand side evaluates to the same exact value `96/85`. -/
theorem deficitRatio_test_eval :
    ((1 + 1 / 20) / (1 + 1 / 50)) * debtRatio Btest Ytest 0
      + deficitRatio Dtest Ytest 1 = 96 / 85 := by
  unfold debtRatio deficitRatio Dtest Btest Ytest
  simp
  norm_num


end MathlibExtTest.Economics.Macro.GovernmentDebtRatio

