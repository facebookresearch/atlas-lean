/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailContinuumEquation





namespace StatMech.FrontierD

noncomputable section

open Filter Topology

theorem one_div_sixVertexRootDensityWeight_upper
    {c : Real} (hc : 2 < c) (x : Real) :
    1 / sixVertexRootDensityWeight c x <=
      sixVertexRootDensityScale c /
        (sixVertexAnisotropyMagnitude c - 1) := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let F := sixVertexBetheIntegratingFactor c x
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hF : 0 < F := sixVertexBetheIntegratingFactor_pos hc x
  have hFlo : d - 1 <= F :=
    (sixVertexBetheIntegratingFactor_bounds hc x).1
  change 1 / (F / s) <= s / (d - 1)
  rw [one_div_div]
  exact div_le_div_of_nonneg_left hs.le (sub_pos.mpr hd) hFlo

theorem abs_selectedDensityIntegral_sub_tailDensityIntegral_le
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (k : Nat) :
    |(∫ y in -Real.pi..Real.pi,
          sixVertexSelectedFiniteRootDensity hc k y) -
        ∫ y in -Real.pi..Real.pi,
          sixVertexTailRootDensity hc htail y| <=
      2 * Real.pi *
        (sixVertexRootDensityScale c /
          (sixVertexAnisotropyMagnitude c - 1)) *
        dist (sixVertexSelectedWeightedDensityMap hc k)
          (sixVertexTailWeightedDensityLimitMap hc htail) := by
  let C := sixVertexRootDensityScale c /
    (sixVertexAnisotropyMagnitude c - 1)
  let dmap := dist (sixVertexSelectedWeightedDensityMap hc k)
    (sixVertexTailWeightedDensityLimitMap hc htail)
  have hC : 0 <= C := by
    exact (div_pos (sixVertexRootDensityScale_pos hc)
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))).le
  have hdmap : 0 <= dmap := dist_nonneg
  have hselected : Continuous (sixVertexSelectedFiniteRootDensity hc k) :=
    continuous_sixVertexFiniteRootDensity hc _ _ _
  have hlimit : Continuous (sixVertexTailRootDensity hc htail) :=
    continuous_sixVertexTailRootDensity hc htail
  have hselectedInt : IntervalIntegrable
      (sixVertexSelectedFiniteRootDensity hc k) MeasureTheory.volume
      (-Real.pi) Real.pi := hselected.intervalIntegrable _ _
  have hlimitInt : IntervalIntegrable
      (sixVertexTailRootDensity hc htail) MeasureTheory.volume
      (-Real.pi) Real.pi := hlimit.intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hselectedInt hlimitInt]
  have hbound :
      ‖∫ y in -Real.pi..Real.pi,
          (sixVertexSelectedFiniteRootDensity hc k y -
            sixVertexTailRootDensity hc htail y)‖ <=
        (C * dmap) * |Real.pi - (-Real.pi)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hy
    have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := ⟨hy.1.le, hy.2⟩
    have hinv : |1 / sixVertexRootDensityWeight c y| <= C := by
      rw [abs_of_pos (one_div_pos.mpr
        (sixVertexRootDensityWeight_pos hc y))]
      exact one_div_sixVertexRootDensityWeight_upper hc y
    have hmap : dist
        ((sixVertexSelectedWeightedDensityMap hc k) ⟨y, hyIcc⟩)
        ((sixVertexTailWeightedDensityLimitMap hc htail) ⟨y, hyIcc⟩) <=
        dmap := by
      exact ((ContinuousMap.dist_le hdmap).1 le_rfl) ⟨y, hyIcc⟩
    rw [Real.dist_eq] at hmap
    have hrewrite :
        sixVertexSelectedFiniteRootDensity hc k y -
            sixVertexTailRootDensity hc htail y =
          (1 / sixVertexRootDensityWeight c y) *
            ((sixVertexSelectedWeightedDensityMap hc k) ⟨y, hyIcc⟩ -
              (sixVertexTailWeightedDensityLimitMap hc htail) ⟨y, hyIcc⟩) := by
      rw [← sixVertexRootDensityWeight_mul_tailRootDensity_of_mem
        hc htail hyIcc]
      dsimp [sixVertexSelectedWeightedDensityMap]
      field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
    rw [hrewrite, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hinv hmap (abs_nonneg _) hC
  rw [Real.norm_eq_abs] at hbound
  have hlength : |Real.pi - -Real.pi| = 2 * Real.pi := by
    rw [abs_of_pos (by linarith [Real.pi_pos])]
    ring
  rw [hlength] at hbound
  dsimp [C, dmap] at hbound ⊢
  nlinarith

theorem intervalIntegral_sixVertexTailRootDensity
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    ∫ y in -Real.pi..Real.pi,
      sixVertexTailRootDensity hc htail y = 1 / 2 := by
  have hdist : Tendsto (fun k =>
      dist (sixVertexSelectedWeightedDensityMap hc k)
        (sixVertexTailWeightedDensityLimitMap hc htail)) atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).1
      (tendsto_sixVertexSelectedWeightedDensityMap hc htail)
  let C := 2 * Real.pi *
    (sixVertexRootDensityScale c /
      (sixVertexAnisotropyMagnitude c - 1))
  have hupper : Tendsto (fun k => C *
      dist (sixVertexSelectedWeightedDensityMap hc k)
        (sixVertexTailWeightedDensityLimitMap hc htail)) atTop (nhds 0) := by
    simpa using hdist.const_mul C
  have hInt : Tendsto (fun k =>
      ∫ y in -Real.pi..Real.pi,
        sixVertexSelectedFiniteRootDensity hc k y) atTop
      (nhds (∫ y in -Real.pi..Real.pi,
        sixVertexTailRootDensity hc htail y)) := by
    apply (tendsto_iff_dist_tendsto_zero).2
    have habs : Tendsto (fun k =>
        |(∫ y in -Real.pi..Real.pi,
            sixVertexSelectedFiniteRootDensity hc k y) -
          ∫ y in -Real.pi..Real.pi,
            sixVertexTailRootDensity hc htail y|) atTop (nhds 0) := by
      apply squeeze_zero'
      · filter_upwards [] with k
        exact abs_nonneg _
      · filter_upwards [] with k
        exact abs_selectedDensityIntegral_sub_tailDensityIntegral_le hc htail k
      · exact hupper
    simpa [Real.dist_eq, C] using habs
  have hhalf (k : Nat) :
      ∫ y in -Real.pi..Real.pi,
        sixVertexSelectedFiniteRootDensity hc k y = 1 / 2 := by
    let n := k + (k + 1)
    have hwidth : sixVertexFourWidth 0 k = 2 * (n + 1) := by
      dsimp [n, sixVertexFourWidth]
      omega
    exact intervalIntegral_halfFilledFiniteRootDensity hc
      (sixVertexFourWidth_pos 0 k) hwidth _
  have hconst : Tendsto (fun _ : Nat => (1 / 2 : Real)) atTop
      (nhds (1 / 2 : Real)) := tendsto_const_nhds
  have heq : (fun k =>
      ∫ y in -Real.pi..Real.pi,
        sixVertexSelectedFiniteRootDensity hc k y) =
      fun _ => (1 / 2 : Real) := by
    funext k
    exact hhalf k
  rw [heq] at hInt
  exact tendsto_nhds_unique hInt hconst



theorem sixVertexRootDensity_continuumEquation_unique
    {c : Real} (hc : 2 < c) {rho sigma : Real → Real}
    (hrho : Continuous rho) (hsigma : Continuous sigma)
    (hrhoMass : (∫ y in -Real.pi..Real.pi, rho y) = 1 / 2)
    (hsigmaMass : (∫ y in -Real.pi..Real.pi, sigma y) = 1 / 2)
    (hrhoEq : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      sixVertexRootDensityWeight c x * rho x =
        sixVertexRootDensityWeight c x / (2 * Real.pi) -
          (1 / (2 * Real.pi)) *
            ∫ y in -Real.pi..Real.pi,
              sixVertexRootDensityKernel c x y * rho y)
    (hsigmaEq : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      sixVertexRootDensityWeight c x * sigma x =
        sixVertexRootDensityWeight c x / (2 * Real.pi) -
          (1 / (2 * Real.pi)) *
            ∫ y in -Real.pi..Real.pi,
              sixVertexRootDensityKernel c x y * sigma y) :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi, rho x = sigma x := by
  let e : Real → Real := fun x =>
    sixVertexRootDensityWeight c x * (rho x - sigma x)
  have hweight : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have he : Continuous e := hweight.mul (hrho.sub hsigma)
  have hnonempty : (Set.Icc (-Real.pi) Real.pi).Nonempty :=
    Set.nonempty_Icc.2 (by linarith [Real.pi_pos])
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn hnonempty
    he.abs.continuousOn
  let E := |e x0|
  have hE : 0 <= E := abs_nonneg _
  have hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| <= E :=
    fun y hy => hmax hy
  have hrhoBaseInt : IntervalIntegrable rho MeasureTheory.volume
      (-Real.pi) Real.pi := hrho.intervalIntegrable _ _
  have hsigmaBaseInt : IntervalIntegrable sigma MeasureTheory.volume
      (-Real.pi) Real.pi := hsigma.intervalIntegrable _ _
  have hmass :
      ∫ y in -Real.pi..Real.pi,
        e y / sixVertexRootDensityWeight c y = 0 := by
    have heq : (fun y => e y / sixVertexRootDensityWeight c y) =
        fun y => rho y - sigma y := by
      funext y
      dsimp [e]
      field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
    rw [heq, intervalIntegral.integral_sub hrhoBaseInt hsigmaBaseInt,
      hrhoMass, hsigmaMass]
    ring
  have hcontract := sixVertexRootDensityKernel_contraction hc he hE hmass
    hbound x0
  have hrhoInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x0 y * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((lipschitzWith_sixVertexRootDensityKernel_right hc x0).continuous.mul
      hrho).intervalIntegrable _ _
  have hsigmaInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x0 y * sigma y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((lipschitzWith_sixVertexRootDensityKernel_right hc x0).continuous.mul
      hsigma).intervalIntegrable _ _
  have hJ :
      (∫ y in -Real.pi..Real.pi,
        (sixVertexRootDensityKernel c x0 y /
          sixVertexRootDensityWeight c y) * e y) =
      (∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x0 y * rho y) -
      ∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x0 y * sigma y := by
    rw [show (fun y =>
        (sixVertexRootDensityKernel c x0 y /
          sixVertexRootDensityWeight c y) * e y) =
      fun y => sixVertexRootDensityKernel c x0 y * rho y -
        sixVertexRootDensityKernel c x0 y * sigma y by
          funext y
          dsimp [e]
          field_simp [(sixVertexRootDensityWeight_pos hc y).ne']]
    rw [intervalIntegral.integral_sub hrhoInt hsigmaInt]
  have heq0 : e x0 = -(1 / (2 * Real.pi)) *
      ((∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x0 y * rho y) -
        ∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x0 y * sigma y) := by
    dsimp [e]
    rw [mul_sub, hrhoEq x0 hx0, hsigmaEq x0 hx0]
    ring
  have heabs : |e x0| =
      |(1 / (2 * Real.pi)) *
        (∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x0 y /
            sixVertexRootDensityWeight c y) * e y)| := by
    rw [heq0, ← hJ]
    rw [show -(1 / (2 * Real.pi)) *
        (∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x0 y /
            sixVertexRootDensityWeight c y) * e y) =
      -((1 / (2 * Real.pi)) *
        (∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x0 y /
            sixVertexRootDensityWeight c y) * e y)) by ring,
      abs_neg]
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hEcontract : E <= sixVertexRootDensityContractionRate c * E := by
    calc
      E = |e x0| := rfl
      _ = |(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x0 y /
              sixVertexRootDensityWeight c y) * e y)| := heabs
      _ <= sixVertexRootDensityContractionRate c * E := hcontract
  have hEzero : E = 0 := by
    nlinarith [hEcontract, hrate.2, hE]
  intro x hx
  have hex : |e x| = 0 := le_antisymm
    ((hbound x hx).trans_eq hEzero) (abs_nonneg _)
  have hezero : e x = 0 := abs_eq_zero.mp hex
  dsimp [e] at hezero
  exact sub_eq_zero.mp (mul_eq_zero.mp hezero |>.resolve_left
    (sixVertexRootDensityWeight_pos hc x).ne')

end

end StatMech.FrontierD
