/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.ExponentialGrowth
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Analysis.ODE.ExponentialGrowth

open MathlibExt.Analysis.ODE.ExponentialGrowth

/-- Initial condition at `x₀ = 2`, `r = 1`. -/
example : expGrowthPath 2 1 0 = 2 := expGrowthPath_zero 2 1

/-- Derivative of the path with `x₀ = 3`, `r = 2` at `t = 0` is `2 * 3 = 6`. -/
example : HasDerivAt (expGrowthPath 3 2) 6 0 := by
  have h := expGrowthPath_hasDerivAt 3 2 0
  have h0 : expGrowthPath 3 2 0 = 3 := expGrowthPath_zero 3 2
  rw [h0] at h
  norm_num at h
  exact h

/-- The `r = 0` path is constant. -/
example : expGrowthPath 5 0 1 = 5 := by
  simp [expGrowthPath, Real.exp_zero]

end MathlibExtTest.Analysis.ODE.ExponentialGrowth
