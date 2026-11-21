/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LinearSystemBackwardError
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open MathlibExt.Analysis.InnerProductSpace.LinearSystemBackwardError

namespace MathlibExtTest.Analysis.InnerProductSpace.LinearSystemBackwardError

/-- For `A = 0`, `b = 1` and the candidate `x̂ = 1` on `ℝ`, the residual is `-1`, so the least
backward error is `1`. -/
example : IsLeast {t : ℝ | ∃ E : ℝ →L[ℝ] ℝ, (0 + E) 1 = 1 ∧ ‖E‖ = t} 1 := by
  simpa using isLeast_norm_backward_error (𝕜 := ℝ) (0 : ℝ →L[ℝ] ℝ) 1 one_ne_zero

/-- The distance-to-singularity theorem applies on Euclidean space `ℝ²`. -/
example (A : (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))ˣ) :
    IsLeast {t : ℝ | ∃ E : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      ¬ IsUnit ((↑A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) - E) ∧ ‖E‖ = t}
      ‖(↑A⁻¹ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))‖⁻¹ :=
  isLeast_norm_of_not_isUnit_sub A

/-- For the identity on `ℝ`, the nearest singular operator is at distance `1`. -/
example : IsLeast {t : ℝ | ∃ E : ℝ →L[ℝ] ℝ, ¬ IsUnit ((1 : ℝ →L[ℝ] ℝ) - E) ∧ ‖E‖ = t} 1 := by
  simpa using isLeast_norm_of_not_isUnit_sub (𝕜 := ℝ) (1 : (ℝ →L[ℝ] ℝ)ˣ)

end MathlibExtTest.Analysis.InnerProductSpace.LinearSystemBackwardError
