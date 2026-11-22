/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LinearGaussianBackwardModel

@[expose] public section

/-!
# Tests for the backward model of a linear Gaussian additive noise model
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.LinearGaussianBackwardModel

namespace MathlibExtTest.Probability.LinearGaussianBackwardModel

/-- Non-vacuity: two independent standard Gaussian coordinates on `ℝ × ℝ` satisfy the
hypotheses, so `Y = 2 X + N` has a backward model. -/
example : ∃ ψ : ℝ, IndepFun (fun ω : ℝ × ℝ => ω.1 - ψ * (2 * ω.1 + ω.2))
    (fun ω : ℝ × ℝ => 2 * ω.1 + ω.2) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  refine exists_indepFun_backward_of_map_eq_gaussianReal (X := Prod.fst) (N := Prod.snd)
    measurable_fst measurable_snd ?_ (m₁ := 0) (m₂ := 0) (v₁ := 1) (v₂ := 1) ?_ ?_ 2
  · exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  · simp
  · simp

end MathlibExtTest.Probability.LinearGaussianBackwardModel
