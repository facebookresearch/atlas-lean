/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MetricSpace.GromovHyperbolic

@[expose] public section

namespace MathlibExtTest.GromovHyperbolic

open Metric

/-- Regression test for the Gromov-product basepoint order: the real line is an `ℝ`-tree, so it
is `0`-hyperbolic. `Metric.gromovProduct w x y` is the product of `x` and `y` at the basepoint
`w`. Reading the basepoint as the third argument mixes basepoints in the four-point inequality,
and `ℝ` then fails it for every `δ`: at `w = 0`, `x = z = -R`, `y = R` it reads `R - δ ≤ 0`. -/
theorem real_isDeltaHyperbolic_zero : IsDeltaHyperbolic ℝ 0 := by
  refine ⟨le_rfl, fun w x y z => ?_⟩
  simp only [gromovProduct_eq, Real.dist_eq, sub_zero]
  by_contra! h
  have h₁ := h.trans_le (min_le_left _ _)
  have h₂ := h.trans_le (min_le_right _ _)
  rcases abs_cases (w - x) with ⟨h₃, h₃'⟩ | ⟨h₃, h₃'⟩ <;>
  rcases abs_cases (w - y) with ⟨h₄, h₄'⟩ | ⟨h₄, h₄'⟩ <;>
  rcases abs_cases (w - z) with ⟨h₅, h₅'⟩ | ⟨h₅, h₅'⟩ <;>
  rcases abs_cases (x - y) with ⟨h₆, h₆'⟩ | ⟨h₆, h₆'⟩ <;>
  rcases abs_cases (y - z) with ⟨h₇, h₇'⟩ | ⟨h₇, h₇'⟩ <;>
  rcases abs_cases (x - z) with ⟨h₈, h₈'⟩ | ⟨h₈, h₈'⟩ <;>
  linarith

/-- The real line is Gromov-hyperbolic. -/
example : IsGromovHyperbolic ℝ :=
  ⟨0, real_isDeltaHyperbolic_zero⟩

end MathlibExtTest.GromovHyperbolic
