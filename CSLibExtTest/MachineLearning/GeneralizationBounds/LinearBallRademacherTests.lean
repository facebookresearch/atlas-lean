/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.LinearBallRademacher

open Real
open MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype (rademacherSign)

namespace CSLibExt.MachineLearning.GeneralizationBounds

-- Linear predictors on the real line with `|θ| ≤ 1` and two unit features: `R̂ ≤ √2 / 2`.
example : ((2 : ℝ) ^ 2)⁻¹ * ∑ σ : Fin 2 → Bool,
    (⨆ θ : {θ : ℝ // ‖θ‖ ≤ 1}, (1 / 2 : ℝ) * ∑ i, rademacherSign ℝ σ i * inner ℝ (θ : ℝ) 1) ≤
      1 / 2 * √2 := by
  have h := rademacher_average_linear_ball_le (E := ℝ) (n := 2) (fun _ => 1) (D := 1) zero_le_one
  simpa [Fin.sum_univ_two, one_add_one_eq_two] using h

-- A ball of radius `0` has average at most `0`.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (φ : Fin 3 → E) :
    ((2 : ℝ) ^ 3)⁻¹ * ∑ σ : Fin 3 → Bool,
      (⨆ θ : {θ : E // ‖θ‖ ≤ 0}, (1 / 3 : ℝ) * ∑ i, rademacherSign ℝ σ i * inner ℝ (θ : E) (φ i))
        ≤ 0 := by
  simpa using rademacher_average_linear_ball_le φ le_rfl

end CSLibExt.MachineLearning.GeneralizationBounds
