/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.KeynesianCross
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Macro.KeynesianCross

open MathlibExt.Economics.Macro.KeynesianCross

/-- Concrete Keynesian cross: marginal propensity to consume `1 / 2`, autonomous
expenditure `100`, equilibrium output `200`. Prove by applying `keynesianCross_solution`. -/
theorem keynesianCross_example {Y : ℝ} (h : IsKeynesianEquilibrium (1 / 2) 100 Y) :
    Y = 200 := by
  have hc : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hc1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hsol := keynesianCross_solution hc hc1 h
  norm_num at hsol
  exact hsol

/-- Concrete multiplier: raising autonomous expenditure from `100` to `120` at `c = 1 / 2`
raises equilibrium output by `40 = 20 * 2`. Prove by applying
`keynesianCross_multiplier`. -/
theorem keynesianCross_multiplier_example {Y₁ Y₂ : ℝ}
    (h₁ : IsKeynesianEquilibrium (1 / 2) 100 Y₁)
    (h₂ : IsKeynesianEquilibrium (1 / 2) 120 Y₂) :
    Y₂ - Y₁ = 40 := by
  have hc : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hc1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hmul := keynesianCross_multiplier hc hc1 h₁ h₂
  norm_num at hmul
  exact hmul

end MathlibExtTest.Economics.Macro.KeynesianCross
