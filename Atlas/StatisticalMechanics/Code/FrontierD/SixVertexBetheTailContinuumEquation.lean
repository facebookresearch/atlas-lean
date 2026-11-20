/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailLimit





namespace StatMech.FrontierD

noncomputable section

open Filter Topology

theorem abs_selectedDensityConvolution_sub_tailConvolution_le
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (k : Nat) (x : Real) :
    |(∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y *
            sixVertexSelectedFiniteRootDensity hc k y) -
        ∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y *
            sixVertexTailRootDensity hc htail y| <=
      2 * Real.pi *
        (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) *
        dist (sixVertexSelectedWeightedDensityMap hc k)
          (sixVertexTailWeightedDensityLimitMap hc htail) := by
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  let dmap := dist (sixVertexSelectedWeightedDensityMap hc k)
    (sixVertexTailWeightedDensityLimitMap hc htail)
  have hR : 0 <= R := by
    exact (div_pos
      (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))).le
  have hdmap : 0 <= dmap := dist_nonneg
  have hselected : Continuous (sixVertexSelectedFiniteRootDensity hc k) :=
    continuous_sixVertexFiniteRootDensity hc _ _ _
  have hlimit : Continuous (sixVertexTailRootDensity hc htail) :=
    continuous_sixVertexTailRootDensity hc htail
  have hkernel : Continuous (sixVertexRootDensityKernel c x) :=
    (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
  have hselInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y *
        sixVertexSelectedFiniteRootDensity hc k y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hkernel.mul hselected).intervalIntegrable _ _
  have hlimInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y *
        sixVertexTailRootDensity hc htail y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hkernel.mul hlimit).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hselInt hlimInt]
  have hbound :
      ‖∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x y *
              sixVertexSelectedFiniteRootDensity hc k y -
            sixVertexRootDensityKernel c x y *
              sixVertexTailRootDensity hc htail y)‖ <=
        (R * dmap) * |Real.pi - (-Real.pi)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hy
    have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := ⟨hy.1.le, hy.2⟩
    have hquot :
        |sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y| <= R := by
      rw [sixVertexRootDensityKernel_div_weight hc]
      rw [← Real.norm_eq_abs]
      exact norm_sixVertexTheta_rightDerivative_le hc x y
    have hmap : dist
        ((sixVertexSelectedWeightedDensityMap hc k)
          (⟨y, hyIcc⟩ : Set.Icc (-Real.pi) Real.pi))
        ((sixVertexTailWeightedDensityLimitMap hc htail)
          ⟨y, hyIcc⟩) <= dmap := by
      exact ((ContinuousMap.dist_le hdmap).1 le_rfl) ⟨y, hyIcc⟩
    rw [Real.dist_eq] at hmap
    have hrewrite :
        sixVertexRootDensityKernel c x y *
              sixVertexSelectedFiniteRootDensity hc k y -
            sixVertexRootDensityKernel c x y *
              sixVertexTailRootDensity hc htail y =
          (sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) *
            ((sixVertexSelectedWeightedDensityMap hc k) ⟨y, hyIcc⟩ -
              (sixVertexTailWeightedDensityLimitMap hc htail) ⟨y, hyIcc⟩) := by
      rw [← sixVertexRootDensityWeight_mul_tailRootDensity_of_mem
        hc htail hyIcc]
      dsimp [sixVertexSelectedWeightedDensityMap]
      field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
    rw [hrewrite, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hquot hmap (abs_nonneg _) hR
  rw [Real.norm_eq_abs] at hbound
  have hlength : |Real.pi - -Real.pi| = 2 * Real.pi := by
    rw [abs_of_pos (by linarith [Real.pi_pos])]
    ring
  rw [hlength] at hbound
  dsimp [R, dmap] at hbound ⊢
  nlinarith

theorem tendsto_sixVertexSelectedDensityConvolution_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (x : Real) :
    Tendsto (fun k =>
      ∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x y *
          sixVertexSelectedFiniteRootDensity hc k y) atTop
      (nhds (∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x y *
          sixVertexTailRootDensity hc htail y)) := by
  have hdist : Tendsto (fun k =>
      dist (sixVertexSelectedWeightedDensityMap hc k)
        (sixVertexTailWeightedDensityLimitMap hc htail)) atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).1
      (tendsto_sixVertexSelectedWeightedDensityMap hc htail)
  let C := 2 * Real.pi *
    (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1))
  have hupper : Tendsto (fun k => C *
      dist (sixVertexSelectedWeightedDensityMap hc k)
        (sixVertexTailWeightedDensityLimitMap hc htail)) atTop (nhds 0) := by
    simpa using hdist.const_mul C
  apply (tendsto_iff_dist_tendsto_zero).2
  have habs : Tendsto (fun k =>
      |(∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y *
            sixVertexSelectedFiniteRootDensity hc k y) -
        ∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y *
            sixVertexTailRootDensity hc htail y|) atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [] with k
      exact abs_nonneg _
    · filter_upwards [] with k
      exact abs_selectedDensityConvolution_sub_tailConvolution_le
        hc htail k x
    · exact hupper
  simpa [Real.dist_eq, C] using habs

theorem sixVertexTailRootDensity_continuumEquation
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexRootDensityWeight c x *
        sixVertexTailRootDensity hc htail x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) *
          ∫ y in -Real.pi..Real.pi,
            sixVertexRootDensityKernel c x y *
              sixVertexTailRootDensity hc htail y := by
  let A : Nat → Real := fun k => sixVertexRootDensityWeight c x *
    sixVertexSelectedFiniteRootDensity hc k x
  let B : Nat → Real := fun k =>
    sixVertexRootDensityWeight c x / (2 * Real.pi) -
      (1 / (2 * Real.pi)) *
        ∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y *
            sixVertexSelectedFiniteRootDensity hc k y
  let ALim := sixVertexRootDensityWeight c x *
    sixVertexTailRootDensity hc htail x
  let BLim := sixVertexRootDensityWeight c x / (2 * Real.pi) -
    (1 / (2 * Real.pi)) *
      ∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x y *
          sixVertexTailRootDensity hc htail y
  have hA : Tendsto A atTop (nhds ALim) := by
    exact tendsto_sixVertexSelectedWeightedDensity_at hc htail hx
  have hI := tendsto_sixVertexSelectedDensityConvolution_tail hc htail x
  have hB : Tendsto B atTop (nhds BLim) := by
    dsimp [B, BLim]
    exact tendsto_const_nhds.sub (hI.const_mul (1 / (2 * Real.pi)))
  have herror :=
    (sixVertexTailConvolutionError_fourWidth_tendsto_zero hc htail).div_const
      (2 * Real.pi)
  have habs : Tendsto (fun k => |A k - B k|) atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [] with k
      exact abs_nonneg _
    · filter_upwards [] with k
      exact sixVertexSelectedFiniteRootDensity_approximateEquation_tail
        hc htail k x
    · simpa using herror
  have hzero : Tendsto (fun k => A k - B k) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 (by
      simpa [Function.comp_def] using habs)
  have hlim : Tendsto (fun k => A k - B k) atTop (nhds (ALim - BLim)) :=
    hA.sub hB
  have heq : ALim - BLim = 0 := tendsto_nhds_unique hlim hzero
  dsimp [ALim, BLim] at heq
  linarith

end

end StatMech.FrontierD
