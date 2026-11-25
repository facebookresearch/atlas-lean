/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Complex.Convex
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

-- Reversing the unit circle: still piecewise `C¹`, and it winds `-1` times around the origin.
example : (circlePath 0 1).symm.IsPiecewiseC1 ∧ windingNumber (circlePath 0 1).symm 0 = -1 :=
  ⟨(isPiecewiseC1_circlePath 0 1).symm, by
    rw [windingNumber_symm, windingNumber_circlePath_of_mem_ball (mem_ball_self one_pos)]⟩

/-! ### A genuinely piecewise `C¹` path

The backtracking path `0 → 1 → 0` is a concatenation of two segments. It has a corner at the
parameter `1/2`, so it is not `C¹` on `[0, 1]`, and every subdivision witnessing
`Path.IsPiecewiseC1` for it has at least two pieces. -/

namespace WindingNumberTest

open Filter Topology

/-- The closed path `0 → 1 → 0` along the real axis. -/
noncomputable def backtrack : Path (0 : ℂ) 0 := (Path.segment 0 1).trans (Path.segment 1 0)

theorem isPiecewiseC1_backtrack : backtrack.IsPiecewiseC1 :=
  (Path.isPiecewiseC1_segment 0 1).trans (Path.isPiecewiseC1_segment 1 0)

theorem backtrack_extend {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    backtrack.extend t = ((1 - |2 * t - 1| : ℝ) : ℂ) := by
  rcases le_total t (1 / 2) with h | h
  · rw [backtrack, Path.extend_trans_of_le_half _ _ h,
      Path.eqOn_extend_segment _ _ ⟨by linarith [ht.1], by linarith⟩,
      AffineMap.lineMap_apply_module, abs_of_nonpos (by linarith)]
    simp only [real_smul]
    push_cast
    ring
  · rw [backtrack, Path.extend_trans_of_half_le _ _ h,
      Path.eqOn_extend_segment _ _ ⟨by linarith, by linarith [ht.2]⟩,
      AffineMap.lineMap_apply_module, abs_of_nonneg (by linarith)]
    simp only [real_smul]
    push_cast
    ring

-- The corner: the backtracking path is not `C¹` on `[0, 1]`, since its real part is
-- `t ↦ 1 - |2t - 1|` near `1/2`.
theorem not_contDiffOn_backtrack : ¬ContDiffOn ℝ 1 backtrack.extend (Icc 0 1) := by
  intro h
  have hI : Icc (0 : ℝ) 1 ∈ 𝓝 (1 / 2) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hd : DifferentiableAt ℝ backtrack.extend (1 / 2) :=
    (h.differentiableOn one_ne_zero).differentiableAt hI
  have hre : DifferentiableAt ℝ (fun t : ℝ => 1 - |2 * t - 1|) (1 / 2) := by
    refine (reCLM.differentiableAt.comp _ hd).congr_of_eventuallyEq ?_
    filter_upwards [hI] with t ht
    simp [backtrack_extend ht]
  have habs : DifferentiableAt ℝ (fun t : ℝ => |2 * t - 1|) (1 / 2) := by
    simpa using (differentiableAt_const (1 : ℝ)).sub hre
  have hlin : DifferentiableAt ℝ (fun u : ℝ => (u + 1) / 2) 0 := by fun_prop
  have habs' : DifferentiableAt ℝ (fun t : ℝ => |2 * t - 1|) ((0 + 1) / 2) := by
    convert habs using 2
    norm_num
  refine not_differentiableAt_abs_zero ((habs'.comp (0 : ℝ) hlin).congr_of_eventuallyEq ?_)
  filter_upwards with u
  simp only [Function.comp_apply]
  ring_nf

-- So the piecewise `C¹` predicate is not just "`C¹` on `[0, 1]`".
example : backtrack.IsPiecewiseC1 ∧ ¬ContDiffOn ℝ 1 backtrack.extend (Icc 0 1) :=
  ⟨isPiecewiseC1_backtrack, not_contDiffOn_backtrack⟩

theorem range_backtrack_subset : range backtrack ⊆ {z : ℂ | z.re ≤ 1} := by
  rintro _ ⟨t, rfl⟩
  rw [← Path.extend_extends' backtrack t, backtrack_extend t.2]
  simp [abs_nonneg]

-- Its winding number around `2` is `0`: the half-plane `re > 1` misses the path, contains `2` and
-- is unbounded, so the component of `2` in the complement of the path is unbounded.
example : windingNumber backtrack 2 = 0 := by
  refine windingNumber_eq_zero_of_not_isBounded isPiecewiseC1_backtrack fun hb => ?_
  have hS : {w : ℂ | 1 < w.re} ⊆ connectedComponentIn (range backtrack)ᶜ 2 :=
    (convex_halfSpace_re_gt 1).isPreconnected.subset_connectedComponentIn (by norm_num)
      fun w hw hwγ =>
        not_le.2 (show 1 < w.re from hw) (show w.re ≤ 1 from range_backtrack_subset hwγ)
  obtain ⟨C, hC⟩ := (hb.subset hS).exists_norm_le
  have hmem : ((max C 1 + 1 : ℝ) : ℂ) ∈ {w : ℂ | 1 < w.re} := by
    show 1 < ((max C 1 + 1 : ℝ) : ℂ).re
    rw [ofReal_re]
    linarith [le_max_right C 1]
  have := hC _ hmem
  rw [norm_real, Real.norm_of_nonneg (by linarith [le_max_right C 1])] at this
  linarith [le_max_left C 1]

-- Off the path, its winding number is an integer.
example {z : ℂ} (hz : z ∉ range backtrack) : ∃ n : ℤ, windingNumber backtrack z = n :=
  exists_windingNumber_eq_intCast isPiecewiseC1_backtrack hz

end WindingNumberTest

#print axioms Path.IsPiecewiseC1.trans
#print axioms Path.IsPiecewiseC1.symm
#print axioms Path.isPiecewiseC1_segment
#print axioms windingNumber_symm
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
