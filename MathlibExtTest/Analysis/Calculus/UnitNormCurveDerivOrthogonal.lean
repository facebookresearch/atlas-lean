/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.UnitNormCurveDerivOrthogonal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases

open scoped InnerProductSpace

namespace MathlibExt.Analysis.Calculus.UnitNormCurveDerivOrthogonalWanted

-- The equatorial circle has unit norm and nonzero velocity.
private noncomputable def equator (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[Real.cos t, Real.sin t, 0]

example (t : ℝ) : ⟪deriv equator t, equator t⟫_ℝ = 0 := by
  apply inner_deriv_self_eq_zero_of_norm_eq_one
  · apply differentiable_euclidean.mpr
    intro i
    fin_cases i
    · exact Real.differentiable_cos
    · exact Real.differentiable_sin
    · exact differentiable_const _
  · intro s
    simp [equator, EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.norm_eq_abs,
      Real.cos_sq_add_sin_sq]

end MathlibExt.Analysis.Calculus.UnitNormCurveDerivOrthogonalWanted
