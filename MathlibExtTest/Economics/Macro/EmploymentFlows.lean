/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Macro.EmploymentFlows
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Macro.EmploymentFlows` -/

namespace MathlibExtTest.Economics.Macro.EmploymentFlows

open MathlibExt.Economics.Macro.EmploymentFlows

example : (1 / 10 : ℝ) = (0.03 : ℝ) / (0.03 + 0.27) := by
  have hflow : (0.03 : ℝ) * (1 - 1 / 10) = (0.27 : ℝ) * (1 / 10) := by norm_num
  exact steady_unemployment (by norm_num) (by norm_num) (by norm_num) hflow

example : (0.03 : ℝ) * (1 - (0.03 : ℝ) / (0.03 + 0.27)) = (0.27 : ℝ) * ((0.03 : ℝ) / (0.03 + 0.27)) ∧ ((0.03 : ℝ) / (0.03 + 0.27)) ≤ 1 := by
  have h := steady_unemployment_satisfies (s := (0.03 : ℝ)) (f := (0.27 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.2⟩

end MathlibExtTest.Economics.Macro.EmploymentFlows
