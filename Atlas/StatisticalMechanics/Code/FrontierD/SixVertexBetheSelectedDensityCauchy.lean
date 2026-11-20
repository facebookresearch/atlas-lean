/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailSelectedDensity









open Filter Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexSelectedDensityCauchyError (c : Real) (k l : Nat) : Real :=
  ((sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) +
      sixVertexTailConvolutionError c (sixVertexFourWidth 0 l)) /
    (2 * Real.pi)) /
      (1 - sixVertexRootDensityContractionRate c)


def sixVertexSelectedEmpiricalObservable
    {c : Real} (hc : 2 < c) (f : Real -> Real) (k : Nat) : Real :=
  (∑ j, f (sixVertexHalfFilledBetheRoots hc k j)) /
    (sixVertexFourWidth 0 k : Real)


def sixVertexSelectedObservableQuadratureError
    (c : Real) (C : NNReal) (k : Nat) : Real :=
  (C : Real) * sixVertexFiniteRootDensityUniformBound c *
    (1 / ((sixVertexFourWidth 0 k : Real) *
      sixVertexTailFiniteDensityFloor c)) * (2 * Real.pi)



def sixVertexSelectedObservableCauchyControl
    (c : Real) (C : NNReal) (B : Real) (k : Nat) : Real :=
  sixVertexSelectedObservableQuadratureError c C k +
    B * (((sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) /
      (2 * Real.pi)) /
        (1 - sixVertexRootDensityContractionRate c)) /
          ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c)) * (2 * Real.pi)


theorem sixVertexRootDensityWeight_lower
    {c : Real} (hc : 2 < c) (x : Real) :
    (sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c <=
      sixVertexRootDensityWeight c x := by
  have hs := sixVertexRootDensityScale_pos hc
  unfold sixVertexRootDensityWeight
  exact div_le_div_of_nonneg_right
    (sixVertexBetheIntegratingFactor_bounds hc x).1 hs.le


theorem sixVertexSelectedFiniteRootDensity_weighted_cauchy_direct_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (k l : Nat) :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) x -
          sixVertexFiniteRootDensity c (sixVertexFourWidth 0 l)
            ((l + 1) + (l + 1)) (sixVertexHalfFilledBetheRoots hc l) x)| <=
        sixVertexSelectedDensityCauchyError c k l := by
  have hkN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
  have hlN : 0 < sixVertexFourWidth 0 l := sixVertexFourWidth_pos 0 l
  have hkhalf : sixVertexFourWidth 0 k =
      2 * ((k + 1) + (k + 1)) := by
    unfold sixVertexFourWidth
    omega
  have hlhalf : sixVertexFourWidth 0 l =
      2 * ((l + 1) + (l + 1)) := by
    unfold sixVertexFourWidth
    omega
  have h := sixVertexFiniteRootDensity_weighted_cauchy_of_pos_tail
    hc htail hkN hlN (by omega) (by omega) hkhalf hlhalf
    (sixVertexHalfFilledBetheRoots_mem_open hc k)
    (sixVertexHalfFilledBetheRoots_mem_open hc l)
    (sixVertexHalfFilledBetheRoots_is_solution hc k)
    (sixVertexHalfFilledBetheRoots_is_solution hc l)
  simpa only [sixVertexSelectedDensityCauchyError] using h


theorem sixVertexSelectedObservableQuadratureError_tendsto_zero
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (C : NNReal) :
    Tendsto (sixVertexSelectedObservableQuadratureError c C)
      atTop (nhds 0) := by
  have hL : 0 < sixVertexRootDensityKernelLipschitzBound c :=
    sixVertexRootDensityKernelLipschitzBound_pos hc
  have h := (sixVertexTailConvolutionError_fourWidth_tendsto_zero hc htail).const_mul
    ((C : Real) / sixVertexRootDensityKernelLipschitzBound c)
  convert h using 1
  · funext k
    unfold sixVertexSelectedObservableQuadratureError
      sixVertexTailConvolutionError
    field_simp [hL.ne']
  · ring


theorem sixVertexSelectedObservableCauchyControl_tendsto_zero
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (C : NNReal) (B : Real) :
    Tendsto (sixVertexSelectedObservableCauchyControl c C B)
      atTop (nhds 0) := by
  have hq := sixVertexSelectedObservableQuadratureError_tendsto_zero
    hc htail C
  have he := sixVertexTailConvolutionError_fourWidth_tendsto_zero hc htail
  have hd := (((he.div_const (2 * Real.pi)).div_const
    (1 - sixVertexRootDensityContractionRate c)).div_const
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c)).const_mul B |>.mul_const (2 * Real.pi)
  simpa only [sixVertexSelectedObservableCauchyControl, zero_add, zero_div,
    zero_mul, mul_zero, add_zero] using hq.add hd


theorem abs_sixVertexSelectedEmpiricalObservable_sub_finiteDensityIntegral_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {f : Real -> Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi)) (k : Nat) :
    |sixVertexSelectedEmpiricalObservable hc f k -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1))
            (sixVertexHalfFilledBetheRoots hc k) y| <=
      sixVertexSelectedObservableQuadratureError c C k := by
  have hN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
  have hhalf : sixVertexFourWidth 0 k =
      2 * ((k + 1) + (k + 1)) := by
    unfold sixVertexFourWidth
    omega
  exact abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_pos_le_tail
    hc htail hN (by omega) hhalf
    (sixVertexHalfFilledBetheRoots_mem_open hc k)
    (sixVertexHalfFilledBetheRoots_is_solution hc k)
    hf hlip hperiodic



theorem abs_selectedFiniteDensityIntegral_sub_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {f : Real -> Real} {B : Real} (hf : Continuous f) (hB : 0 <= B)
    (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B)
    (k l : Nat) :
    |(∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1))
            (sixVertexHalfFilledBetheRoots hc k) y) -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 l)
            ((l + 1) + (l + 1))
            (sixVertexHalfFilledBetheRoots hc l) y| <=
      B * (sixVertexSelectedDensityCauchyError c k l /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) * (2 * Real.pi) := by
  let rhoK := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
    ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k)
  let rhoL := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 l)
    ((l + 1) + (l + 1)) (sixVertexHalfFilledBetheRoots hc l)
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let E := sixVertexSelectedDensityCauchyError c k l
  have hwmin : 0 < wmin := by
    dsimp [wmin]
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hweighted :=
    sixVertexSelectedFiniteRootDensity_weighted_cauchy_direct_tail
      hc htail k l
  have hrhoK : Continuous rhoK :=
    continuous_sixVertexFiniteRootDensity hc _ _ _
  have hrhoL : Continuous rhoL :=
    continuous_sixVertexFiniteRootDensity hc _ _ _
  have hIK : IntervalIntegrable (fun y => f y * rhoK y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hf.mul hrhoK).intervalIntegrable _ _
  have hIL : IntervalIntegrable (fun y => f y * rhoL y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hf.mul hrhoL).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hIK hIL]
  have hnorm :
      ‖∫ y in -Real.pi..Real.pi,
          (f y * rhoK y - f y * rhoL y)‖ <=
        (B * (E / wmin)) * |Real.pi - -Real.pi| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hy
      exact ⟨hy.1.le, hy.2⟩
    have hweight := hweighted y hyIcc
    have hwlower : wmin <= sixVertexRootDensityWeight c y := by
      exact sixVertexRootDensityWeight_lower hc y
    have hdiff : |rhoK y - rhoL y| <= E / wmin := by
      have hwpos := sixVertexRootDensityWeight_pos hc y
      have hmul : wmin * |rhoK y - rhoL y| <= E := by
        calc
          wmin * |rhoK y - rhoL y| <=
              sixVertexRootDensityWeight c y * |rhoK y - rhoL y| :=
            mul_le_mul_of_nonneg_right hwlower (abs_nonneg _)
          _ = |sixVertexRootDensityWeight c y * (rhoK y - rhoL y)| := by
            rw [abs_mul, abs_of_pos hwpos]
          _ <= E := by simpa [rhoK, rhoL, E] using hweight
      exact (le_div_iff₀ hwmin).2 (by simpa [mul_comm] using hmul)
    calc
      ‖f y * rhoK y - f y * rhoL y‖ =
          |f y| * |rhoK y - rhoL y| := by
        rw [show f y * rhoK y - f y * rhoL y =
          f y * (rhoK y - rhoL y) by ring]
        simp only [Real.norm_eq_abs, abs_mul]
      _ <= B * (E / wmin) :=
        mul_le_mul (hfBound y hyIcc) hdiff (abs_nonneg _)
          (by positivity)
  rw [Real.norm_eq_abs] at hnorm
  rw [abs_of_pos (by nlinarith [Real.pi_pos] :
    0 < Real.pi - -Real.pi)] at hnorm
  dsimp [rhoK, rhoL, E, wmin] at hnorm
  convert hnorm using 1 <;> ring



theorem abs_selectedEmpiricalObservable_sub_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {f : Real -> Real} {C : NNReal} {B : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi)) (hB : 0 <= B)
    (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B)
    (k l : Nat) :
    |sixVertexSelectedEmpiricalObservable hc f k -
        sixVertexSelectedEmpiricalObservable hc f l| <=
      sixVertexSelectedObservableQuadratureError c C k +
        B * (sixVertexSelectedDensityCauchyError c k l /
          ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c)) * (2 * Real.pi) +
        sixVertexSelectedObservableQuadratureError c C l := by
  let IK := ∫ y in -Real.pi..Real.pi,
    f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) y
  let IL := ∫ y in -Real.pi..Real.pi,
    f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 l)
      ((l + 1) + (l + 1)) (sixVertexHalfFilledBetheRoots hc l) y
  have hk :=
    abs_sixVertexSelectedEmpiricalObservable_sub_finiteDensityIntegral_le_tail
      hc htail hf hlip hperiodic k
  have hl :=
    abs_sixVertexSelectedEmpiricalObservable_sub_finiteDensityIntegral_le_tail
      hc htail hf hlip hperiodic l
  have hI := abs_selectedFiniteDensityIntegral_sub_le_tail
    hc htail hf hB hfBound k l
  change |_ - IK| <= _ at hk
  change |_ - IL| <= _ at hl
  change |IK - IL| <= _ at hI
  calc
    |sixVertexSelectedEmpiricalObservable hc f k -
        sixVertexSelectedEmpiricalObservable hc f l| =
      |(sixVertexSelectedEmpiricalObservable hc f k - IK) +
        (IK - IL) +
        (IL - sixVertexSelectedEmpiricalObservable hc f l)| := by ring_nf
    _ <= |sixVertexSelectedEmpiricalObservable hc f k - IK| +
        |IK - IL| +
        |IL - sixVertexSelectedEmpiricalObservable hc f l| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ <= _ := by
      rw [abs_sub_comm IL]
      gcongr



theorem abs_selectedEmpiricalObservable_sub_le_cauchyControl_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {f : Real -> Real} {C : NNReal} {B : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi)) (hB : 0 <= B)
    (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B)
    (k l : Nat) :
    |sixVertexSelectedEmpiricalObservable hc f k -
        sixVertexSelectedEmpiricalObservable hc f l| <=
      sixVertexSelectedObservableCauchyControl c C B k +
        sixVertexSelectedObservableCauchyControl c C B l := by
  have h := abs_selectedEmpiricalObservable_sub_le_tail
    hc htail hf hlip hperiodic hB hfBound k l
  calc
    |sixVertexSelectedEmpiricalObservable hc f k -
        sixVertexSelectedEmpiricalObservable hc f l| <=
        sixVertexSelectedObservableQuadratureError c C k +
          B * (sixVertexSelectedDensityCauchyError c k l /
            ((sixVertexAnisotropyMagnitude c - 1) /
              sixVertexRootDensityScale c)) * (2 * Real.pi) +
          sixVertexSelectedObservableQuadratureError c C l := h
    _ = sixVertexSelectedObservableCauchyControl c C B k +
        sixVertexSelectedObservableCauchyControl c C B l := by
      unfold sixVertexSelectedObservableCauchyControl
        sixVertexSelectedDensityCauchyError
      ring



theorem exists_tendsto_sixVertexSelectedEmpiricalObservable_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {f : Real -> Real} {C : NNReal} {B : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi)) (hB : 0 <= B)
    (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B) :
    ∃ a : Real, Tendsto (sixVertexSelectedEmpiricalObservable hc f)
      atTop (nhds a) := by
  have hcontrol := sixVertexSelectedObservableCauchyControl_tendsto_zero
    hc htail C B
  have hcauchy : CauchySeq (sixVertexSelectedEmpiricalObservable hc f) := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hcontrol)
      (epsilon / 2) (by positivity)
    refine ⟨N, fun k hk l hl => ?_⟩
    rw [Real.dist_eq]
    have hk' := hN k hk
    have hl' := hN l hl
    rw [Real.dist_eq, sub_zero] at hk' hl'
    have hk'' : sixVertexSelectedObservableCauchyControl c C B k <
        epsilon / 2 := (le_abs_self _).trans_lt hk'
    have hl'' : sixVertexSelectedObservableCauchyControl c C B l <
        epsilon / 2 := (le_abs_self _).trans_lt hl'
    exact (abs_selectedEmpiricalObservable_sub_le_cauchyControl_tail
      hc htail hf hlip hperiodic hB hfBound k l).trans_lt (by linarith)
  exact cauchySeq_tendsto_of_complete hcauchy

end

end StatMech.FrontierD
