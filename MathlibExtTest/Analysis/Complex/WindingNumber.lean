/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.WindingNumber

set_option autoImplicit false

open Complex Metric Set

-- The unit circle is a closed piecewise `C¹` path.
example : (circlePath 0 1).IsPiecewiseC1 := isPiecewiseC1_circlePath 0 1

-- The unit circle winds once around the origin ...
example : windingNumber (circlePath 0 1) 0 = 1 :=
  windingNumber_circlePath_of_mem_ball (mem_ball_self one_pos)

-- ... and not at all around `2`, outside the closed unit disc.
example : windingNumber (circlePath 0 1) 2 = 0 :=
  windingNumber_circlePath_of_notMem_closedBall zero_le_one (by
    rw [mem_closedBall_zero_iff, Complex.norm_two]
    norm_num)

-- `∫_{|z| = 1} z⁻¹ dz = 2πi`, computed through the curve integral.
example : ∫ᶜ z in circlePath 0 1, z⁻¹ • ContinuousLinearMap.id ℂ ℂ = 2 * Real.pi * I := by
  rw [curveIntegral_circlePath]
  simpa using circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self (one_pos (α := ℝ)))
    (c := (0 : ℂ))

-- Off the path, the winding number is an integer, locally constant, and zero near infinity.
example {z : ℂ} (hz : z ∉ range (circlePath 0 1)) : ∃ n : ℤ, windingNumber (circlePath 0 1) z = n :=
  exists_windingNumber_eq_intCast (isPiecewiseC1_circlePath 0 1) hz

example {z : ℂ} (hz : z ∉ range (circlePath 0 1)) :
    ∀ᶠ w in nhds z, windingNumber (circlePath 0 1) w = windingNumber (circlePath 0 1) z :=
  eventually_windingNumber_eq (isPiecewiseC1_circlePath 0 1) hz

example : ∀ᶠ z in Filter.cocompact ℂ, windingNumber (circlePath 0 1) z = 0 :=
  eventually_windingNumber_eq_zero (isPiecewiseC1_circlePath 0 1)

-- The trace of the unit circle lies on the unit sphere.
example : range (circlePath 0 1) ⊆ sphere 0 1 := by
  simpa using range_circlePath_subset 0 1

#print axioms Path.IsPiecewiseC1.of_contDiffOn
#print axioms exists_windingNumber_eq_intCast
#print axioms eventually_windingNumber_eq
#print axioms eventually_windingNumber_eq_zero
#print axioms windingNumber_eq_of_isPreconnected
#print axioms windingNumber_eq_zero_of_not_isBounded
#print axioms differentiableOn_curveIntegral
#print axioms differentiableOn_curveIntegral_div_sub
#print axioms tendsto_curveIntegral_div_sub_cocompact
#print axioms curveIntegral_dslope_of_notMem
#print axioms isPiecewiseC1_circlePath
#print axioms range_circlePath_subset
#print axioms curveIntegral_circlePath
#print axioms windingNumber_circlePath_of_mem_ball
#print axioms windingNumber_circlePath_of_notMem_closedBall
