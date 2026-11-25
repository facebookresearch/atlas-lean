/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.ExpNegSqrtNormSelfConvolutionLimit

/-! # Tests for the self-convolution limit on the Euclidean plane -/

namespace MathlibExtTest.Analysis.SpecificLimits.ExpNegSqrtNormSelfConvolutionLimit

open Filter MeasureTheory
open MathlibExt.Analysis.SpecificLimits.ExpNegSqrtNormSelfConvolutionLimitWanted
open scoped Convolution

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

example : f (0 : Plane) = 1 := by simp [f]

example (x : Plane) : 0 < f x := Real.exp_pos _

-- The norm filter gives the ordinary limit along a unit ray.
example (u : Plane) (hu : ‖u‖ = 1) :
    Tendsto (fun t : ℝ => ((f ⋆ f) (t • u)) / f (t • u)) atTop
      (nhds (2 * ∫ x : Plane, f x)) := by
  refine tendsto_convolution_self_div_atTop_norm.comp (tendsto_comap_iff.mpr ?_)
  apply tendsto_id.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [norm_smul, hu, Real.norm_eq_abs, abs_of_nonneg ht]

end MathlibExtTest.Analysis.SpecificLimits.ExpNegSqrtNormSelfConvolutionLimit
