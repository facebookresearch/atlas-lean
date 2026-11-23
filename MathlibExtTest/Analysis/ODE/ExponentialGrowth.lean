/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.ExponentialGrowth
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

/-- Uniqueness, decaying case: a solution of `x' = -2 * x` with `x 0 = 3` is
`3 * exp (-2 * t)`. -/
example (x : ℝ → ℝ) (hx : ∀ t, HasDerivAt x (-2 * x t) t) (h0 : x 0 = 3) (t : ℝ) :
    x t = 3 * Real.exp (-2 * t) := by
  rw [eq_expGrowthPath_of_hasDerivAt hx t, h0, expGrowthPath]

/-- Uniqueness, growing case: no sign hypothesis is needed, so a solution of `x' = x`
with `x 0 = 1` is `exp t`. -/
example (x : ℝ → ℝ) (hx : ∀ t, HasDerivAt x (1 * x t) t) (h0 : x 0 = 1) (t : ℝ) :
    x t = Real.exp t := by
  rw [eq_expGrowthPath_of_hasDerivAt hx t, h0]
  simp [expGrowthPath]

/-- A solution of `x' = r * x` that vanishes at `0` vanishes everywhere. -/
example (r : ℝ) (x : ℝ → ℝ) (hx : ∀ t, HasDerivAt x (r * x t) t) (h0 : x 0 = 0) (t : ℝ) :
    x t = 0 := by
  rw [eq_expGrowthPath_of_hasDerivAt hx t, h0]
  simp [expGrowthPath]

/-- The concrete profile `3 * exp (-2 * t)` solves `x' = -2 * x`, and uniqueness recovers
it from its derivative and its initial value `3`. -/
example (t : ℝ) : 3 * Real.exp (-2 * t) = 3 * Real.exp (-2 * 0) * Real.exp (-2 * t) := by
  have hd : ∀ s, HasDerivAt (fun t => 3 * Real.exp (-2 * t))
      (-2 * (3 * Real.exp (-2 * s))) s := fun s =>
    (((hasDerivAt_id' s).const_mul (-2 : ℝ)).exp.const_mul (3 : ℝ)).congr_deriv (by ring)
  exact eq_expGrowthPath_of_hasDerivAt hd t

end MathlibExtTest.Analysis.ODE.ExponentialGrowth
