/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricJacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus















open Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexRootDensityScale (c : Real) : Real :=
  Real.sqrt (sixVertexAnisotropyMagnitude c ^ 2 - 1)

def sixVertexRootDensityWeight (c x : Real) : Real :=
  sixVertexBetheIntegratingFactor c x / sixVertexRootDensityScale c


def sixVertexRootDensityKernel (c x y : Real) : Real :=
  4 * sixVertexAnisotropyMagnitude c *
      sixVertexBetheIntegratingFactor c x *
      sixVertexBetheIntegratingFactor c y /
    (sixVertexRootDensityScale c *
      sixVertexThetaDerivativeDenominator c x y)



def sixVertexRootDensityKernelFloor (c : Real) : Real :=
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  4 * d * (d - 1) ^ 2 / (s * (4 * (d + 1) ^ 2 + 4))

theorem sixVertexRootDensityScale_pos
    {c : Real} (hc : 2 < c) : 0 < sixVertexRootDensityScale c := by
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  unfold sixVertexRootDensityScale
  exact Real.sqrt_pos.2 (by nlinarith)

theorem sixVertexRootDensityWeight_pos
    {c : Real} (hc : 2 < c) (x : Real) :
    0 < sixVertexRootDensityWeight c x := by
  exact div_pos (sixVertexBetheIntegratingFactor_pos hc x)
    (sixVertexRootDensityScale_pos hc)

theorem sixVertexRootDensityKernel_pos
    {c : Real} (hc : 2 < c) (x y : Real) :
    0 < sixVertexRootDensityKernel c x y := by
  have hd : 0 < sixVertexAnisotropyMagnitude c :=
    (one_lt_sixVertexAnisotropyMagnitude hc).trans' zero_lt_one
  unfold sixVertexRootDensityKernel
  apply div_pos
  · exact mul_pos
      (mul_pos (mul_pos (by positivity) hd)
        (sixVertexBetheIntegratingFactor_pos hc x))
      (sixVertexBetheIntegratingFactor_pos hc y)
  · exact mul_pos (sixVertexRootDensityScale_pos hc)
      (sixVertexThetaDerivativeDenominator_pos hc x y)

theorem sixVertexRootDensityKernelFloor_pos
    {c : Real} (hc : 2 < c) :
    0 < sixVertexRootDensityKernelFloor c := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  dsimp [sixVertexRootDensityKernelFloor]
  positivity

theorem sixVertexBetheIntegratingFactor_bounds
    {c : Real} (hc : 2 < c) (x : Real) :
    sixVertexAnisotropyMagnitude c - 1 ≤
        sixVertexBetheIntegratingFactor c x ∧
      sixVertexBetheIntegratingFactor c x ≤
        sixVertexAnisotropyMagnitude c + 1 := by
  have hlo := Real.neg_one_le_cos x
  have hhi := Real.cos_le_one x
  simp only [sixVertexAnisotropyMagnitude, sixVertexBetheIntegratingFactor]
  constructor <;> linarith

theorem sixVertexThetaDerivativeDenominator_uniform_upper
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexThetaDerivativeDenominator c x y ≤
      4 * (sixVertexAnisotropyMagnitude c + 1) ^ 2 + 4 := by
  rw [sixVertexThetaDerivativeDenominator_eq]
  have hx := sixVertexBetheIntegratingFactor_bounds hc x
  have hy := sixVertexBetheIntegratingFactor_bounds hc y
  have hfx : 0 ≤ sixVertexBetheIntegratingFactor c x :=
    (sixVertexBetheIntegratingFactor_pos hc x).le
  have hfy : 0 ≤ sixVertexBetheIntegratingFactor c y :=
    (sixVertexBetheIntegratingFactor_pos hc y).le
  have hd1 : 0 ≤ sixVertexAnisotropyMagnitude c + 1 := by
    linarith [one_lt_sixVertexAnisotropyMagnitude hc]
  have hprod : sixVertexBetheIntegratingFactor c x *
      sixVertexBetheIntegratingFactor c y ≤
        (sixVertexAnisotropyMagnitude c + 1) ^ 2 := by
    nlinarith [mul_le_mul hx.2 hy.2 hfy hd1]
  have hcos := Real.neg_one_le_cos (x - y)
  nlinarith

theorem sixVertexRootDensityKernelFloor_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexRootDensityKernelFloor c ≤
      sixVertexRootDensityKernel c x y := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let Fx := sixVertexBetheIntegratingFactor c x
  let Fy := sixVertexBetheIntegratingFactor c y
  let D := sixVertexThetaDerivativeDenominator c x y
  let U := 4 * (d + 1) ^ 2 + 4
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hFx : 0 < Fx := sixVertexBetheIntegratingFactor_pos hc x
  have hFy : 0 < Fy := sixVertexBetheIntegratingFactor_pos hc y
  have hD : 0 < D := sixVertexThetaDerivativeDenominator_pos hc x y
  have hU : 0 < U := by dsimp [U]; positivity
  have hFxlo : d - 1 ≤ Fx := (sixVertexBetheIntegratingFactor_bounds hc x).1
  have hFylo : d - 1 ≤ Fy := (sixVertexBetheIntegratingFactor_bounds hc y).1
  have hDle : D ≤ U := sixVertexThetaDerivativeDenominator_uniform_upper hc x y
  have hprod : (d - 1) ^ 2 ≤ Fx * Fy := by
    nlinarith [mul_le_mul hFxlo hFylo (sub_nonneg.mpr hd.le) hFx.le]
  change 4 * d * (d - 1) ^ 2 / (s * U) ≤
    4 * d * Fx * Fy / (s * D)
  rw [div_le_div_iff₀ (mul_pos hs hU) (mul_pos hs hD)]
  have hd0 : 0 ≤ 4 * d * s := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hprod hd0,
    mul_le_mul_of_nonneg_left hDle (by positivity : 0 ≤ 4 * d * Fx * Fy * s)]



theorem sixVertexRootDensityKernel_div_weight
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexRootDensityKernel c x y /
        sixVertexRootDensityWeight c y =
      -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y := by
  have hs := (sixVertexRootDensityScale_pos hc).ne'
  have hFy := (sixVertexBetheIntegratingFactor_pos hc y).ne'
  unfold sixVertexRootDensityKernel sixVertexRootDensityWeight
    sixVertexAnisotropyMagnitude
  field_simp



theorem sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexRootDensityKernel c x y =
      -sixVertexRootDensityWeight c x *
        (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c x y) := by
  have hs := (sixVertexRootDensityScale_pos hc).ne'
  unfold sixVertexRootDensityKernel sixVertexRootDensityWeight
    sixVertexAnisotropyMagnitude
  field_simp


theorem intervalIntegral_sixVertexRootDensityKernel_div_weight
    {c : Real} (hc : 2 < c) (x : Real) :
    ∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y = 2 * Real.pi := by
  let f : Real → Real := fun y => sixVertexTheta c x y
  let f' : Real → Real := fun y =>
    -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
      sixVertexThetaDerivativeDenominator c x y
  have hfderiv : deriv f = f' := by
    funext y
    exact (hasDerivAt_sixVertexTheta_right hc x y).deriv
  have hfdiff : ∀ y ∈ Set.uIcc (-Real.pi) Real.pi,
      DifferentiableAt Real f y := by
    intro y _
    exact (hasDerivAt_sixVertexTheta_right hc x y).differentiableAt
  have hfcont : ContinuousOn f' (Set.uIcc (-Real.pi) Real.pi) := by
    apply Continuous.continuousOn
    dsimp [f']
    apply Continuous.div
    · fun_prop
    · unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
      fun_prop
    · intro y
      exact (sixVertexThetaDerivativeDenominator_pos hc x y).ne'
  have hFTC := intervalIntegral.integral_deriv_eq_sub'
    (a := -Real.pi) (b := Real.pi) f hfderiv hfdiff hfcont
  have hend : f Real.pi - f (-Real.pi) = 2 * Real.pi := by
    have hperiod := sixVertexTheta_add_two_pi_right c x (-Real.pi)
    have harg : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [harg] at hperiod
    dsimp [f]
    linarith
  rw [hend] at hFTC
  calc
    (∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) =
        ∫ y in -Real.pi..Real.pi, f' y := by
          apply intervalIntegral.integral_congr
          intro y _
          exact sixVertexRootDensityKernel_div_weight hc x y
    _ = 2 * Real.pi := hFTC



def sixVertexRootDensityContractionRate (c : Real) : Real :=
  1 - sixVertexRootDensityKernelFloor c *
    sixVertexRootDensityScale c /
      (sixVertexAnisotropyMagnitude c + 1)

theorem sixVertexRootDensityContractionRate_mem_Ico
    {c : Real} (hc : 2 < c) :
    sixVertexRootDensityContractionRate c ∈ Set.Ico 0 1 := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hfloor : 0 < sixVertexRootDensityKernelFloor c :=
    sixVertexRootDensityKernelFloor_pos hc
  have hden : 0 < d + 1 := by linarith
  have hmargin : 0 < sixVertexRootDensityKernelFloor c * s / (d + 1) :=
    div_pos (mul_pos hfloor hs) hden
  have hmargin_le :
      sixVertexRootDensityKernelFloor c * s / (d + 1) ≤ 1 := by
    dsimp [sixVertexRootDensityKernelFloor]
    rw [div_mul_eq_mul_div, div_div]
    rw [div_le_one (mul_pos (mul_pos hs (by positivity)) hden)]
    have hd0 : 0 ≤ d := le_trans (by norm_num) hd.le
    nlinarith [sq_nonneg (d - 1), sq_nonneg (d + 1)]
  dsimp [sixVertexRootDensityContractionRate]
  constructor <;> linarith

theorem sixVertexRootDensity_reciprocalWeight_lower
    {c : Real} (hc : 2 < c) (y : Real) :
    sixVertexRootDensityScale c /
        (sixVertexAnisotropyMagnitude c + 1) ≤
      1 / sixVertexRootDensityWeight c y := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let Fy := sixVertexBetheIntegratingFactor c y
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hFy : 0 < Fy := sixVertexBetheIntegratingFactor_pos hc y
  have hupper : Fy ≤ d + 1 := (sixVertexBetheIntegratingFactor_bounds hc y).2
  have hquot : s / (d + 1) ≤ s / Fy :=
    div_le_div_of_nonneg_left hs.le hFy hupper
  change s / (d + 1) ≤ 1 / (Fy / s)
  rw [one_div_div]
  exact hquot

theorem intervalIntegral_one_div_sixVertexRootDensityWeight_lower
    {c : Real} (hc : 2 < c) :
    2 * Real.pi *
        (sixVertexRootDensityScale c /
          (sixVertexAnisotropyMagnitude c + 1)) ≤
      ∫ y in -Real.pi..Real.pi, 1 / sixVertexRootDensityWeight c y := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  let a := sixVertexRootDensityScale c /
    (sixVertexAnisotropyMagnitude c + 1)
  have hconst : IntervalIntegrable (fun _ : Real => a)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    continuous_const.intervalIntegrable _ _
  have hrecip : IntervalIntegrable
      (fun y : Real => 1 / sixVertexRootDensityWeight c y)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const
    · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
        sixVertexRootDensityScale
      fun_prop
    · intro y
      exact (sixVertexRootDensityWeight_pos hc y).ne'
  have hmono := intervalIntegral.integral_mono_on hab hconst hrecip
    (fun y _ => sixVertexRootDensity_reciprocalWeight_lower hc y)
  have hconstEval :
      (∫ _y in -Real.pi..Real.pi, a) = 2 * Real.pi * a := by
    simp [a]
    ring
  rw [hconstEval] at hmono
  exact hmono



theorem sixVertexRootDensityKernel_contraction
    {c : Real} (hc : 2 < c) {e : Real → Real} {E : Real}
    (he : Continuous e) (hE : 0 ≤ E)
    (hmass : (∫ y in -Real.pi..Real.pi,
      e y / sixVertexRootDensityWeight c y) = 0)
    (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| ≤ E)
    (x : Real) :
    |(1 / (2 * Real.pi)) *
        ∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) * e y| ≤
      sixVertexRootDensityContractionRate c * E := by
  let floor := sixVertexRootDensityKernelFloor c
  let rate := sixVertexRootDensityContractionRate c
  let H : Real → Real := fun y =>
    (sixVertexRootDensityKernel c x y - floor) /
      sixVertexRootDensityWeight c y
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hfloor : 0 < floor := sixVertexRootDensityKernelFloor_pos hc
  have hHnonneg (y : Real) : 0 ≤ H y := by
    exact div_nonneg
      (sub_nonneg.mpr (sixVertexRootDensityKernelFloor_le hc x y))
      (sixVertexRootDensityWeight_pos hc y).le
  have hweightCont : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have hinvWeightCont : Continuous
      (fun y : Real => 1 / sixVertexRootDensityWeight c y) := by
    apply Continuous.div continuous_const hweightCont
    intro y
    exact (sixVertexRootDensityWeight_pos hc y).ne'
  have hkernelCont : Continuous (sixVertexRootDensityKernel c x) := by
    unfold sixVertexRootDensityKernel sixVertexRootDensityScale
      sixVertexBetheIntegratingFactor sixVertexThetaDerivativeDenominator
      sixVertexThetaDenominator sixVertexAnisotropyMagnitude sixVertexDelta
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro y
      exact (mul_pos (sixVertexRootDensityScale_pos hc)
        (sixVertexThetaDerivativeDenominator_pos hc x y)).ne'
  have hkernelQuotCont : Continuous (fun y : Real =>
      sixVertexRootDensityKernel c x y /
        sixVertexRootDensityWeight c y) :=
    hkernelCont.div hweightCont
      (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
  have hfloorInvCont : Continuous (fun y : Real =>
      floor * (1 / sixVertexRootDensityWeight c y)) :=
    continuous_const.mul hinvWeightCont
  have hHcont : Continuous H := by
    apply Continuous.div
    · exact hkernelCont.sub continuous_const
    · exact hweightCont
    · intro y
      exact (sixVertexRootDensityWeight_pos hc y).ne'
  have hfloorTermCont : Continuous (fun y : Real =>
      (floor / sixVertexRootDensityWeight c y) * e y) := by
    exact (continuous_const.div hweightCont
      (fun y => (sixVertexRootDensityWeight_pos hc y).ne')).mul he
  have hHeq :
      (∫ y in -Real.pi..Real.pi,
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
      ∫ y in -Real.pi..Real.pi, H y * e y := by
    have hzero :
        (∫ y in -Real.pi..Real.pi,
          (floor / sixVertexRootDensityWeight c y) * e y) = 0 := by
      have hfactor : (fun y : Real =>
          (floor / sixVertexRootDensityWeight c y) * e y) =
          fun y => floor * (e y / sixVertexRootDensityWeight c y) := by
        funext y
        ring
      rw [hfactor, intervalIntegral.integral_const_mul, hmass, mul_zero]
    rw [show (fun y : Real =>
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
        fun y => H y * e y +
          (floor / sixVertexRootDensityWeight c y) * e y by
      funext y
      dsimp [H]
      ring]
    have hadd := intervalIntegral.integral_add (μ := MeasureTheory.volume)
      ((hHcont.mul he).intervalIntegrable (-Real.pi) Real.pi)
      (hfloorTermCont.intervalIntegrable (-Real.pi) Real.pi)
    change (∫ y in -Real.pi..Real.pi,
        H y * e y + (floor / sixVertexRootDensityWeight c y) * e y) =
      (∫ y in -Real.pi..Real.pi, H y * e y) +
        ∫ y in -Real.pi..Real.pi,
          (floor / sixVertexRootDensityWeight c y) * e y at hadd
    rw [hadd, hzero, add_zero]
  have habsolute :
      |∫ y in -Real.pi..Real.pi, H y * e y| ≤
        ∫ y in -Real.pi..Real.pi, H y * |e y| := by
    calc
      |∫ y in -Real.pi..Real.pi, H y * e y| ≤
          ∫ y in -Real.pi..Real.pi, |H y * e y| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ = ∫ y in -Real.pi..Real.pi, H y * |e y| := by
        apply intervalIntegral.integral_congr
        intro y _
        change |H y * e y| = H y * |e y|
        rw [abs_mul, abs_of_nonneg (hHnonneg y)]
  have hHE :
      (∫ y in -Real.pi..Real.pi, H y * |e y|) ≤
        ∫ y in -Real.pi..Real.pi, H y * E := by
    apply intervalIntegral.integral_mono_on hab
    · exact (hHcont.mul he.abs).intervalIntegrable _ _
    · exact (hHcont.mul continuous_const).intervalIntegrable _ _
    · intro y hy
      exact mul_le_mul_of_nonneg_left (hbound y hy) (hHnonneg y)
  have hHint :
      (∫ y in -Real.pi..Real.pi, H y) ≤
        2 * Real.pi * rate := by
    have hsplit :
        (∫ y in -Real.pi..Real.pi, H y) =
          2 * Real.pi - floor *
            (∫ y in -Real.pi..Real.pi,
              1 / sixVertexRootDensityWeight c y) := by
      rw [show H = fun y =>
          sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y -
            floor * (1 / sixVertexRootDensityWeight c y) by
        funext y
        dsimp [H]
        ring]
      have hsubint := intervalIntegral.integral_sub (μ := MeasureTheory.volume)
          (hkernelQuotCont.intervalIntegrable (-Real.pi) Real.pi)
          (hfloorInvCont.intervalIntegrable (-Real.pi) Real.pi)
      change (∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y -
            floor * (1 / sixVertexRootDensityWeight c y)) =
        (∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) -
          ∫ y in -Real.pi..Real.pi,
            floor * (1 / sixVertexRootDensityWeight c y) at hsubint
      rw [hsubint, intervalIntegral.integral_const_mul,
        intervalIntegral_sixVertexRootDensityKernel_div_weight hc]
    have hvol := intervalIntegral_one_div_sixVertexRootDensityWeight_lower hc
    have hmul := mul_le_mul_of_nonneg_left hvol hfloor.le
    calc
      (∫ y in -Real.pi..Real.pi, H y) =
          2 * Real.pi - floor *
            (∫ y in -Real.pi..Real.pi,
              1 / sixVertexRootDensityWeight c y) := hsplit
      _ ≤ 2 * Real.pi - floor *
          (2 * Real.pi * (sixVertexRootDensityScale c /
            (sixVertexAnisotropyMagnitude c + 1))) :=
        sub_le_sub_left hmul _
      _ = 2 * Real.pi * rate := by
        dsimp [rate, sixVertexRootDensityContractionRate]
        ring
  rw [hHeq]
  have htotal :
      |∫ y in -Real.pi..Real.pi, H y * e y| ≤
        2 * Real.pi * rate * E := by
    calc
      _ ≤ ∫ y in -Real.pi..Real.pi, H y * |e y| := habsolute
      _ ≤ ∫ y in -Real.pi..Real.pi, H y * E := hHE
      _ = (∫ y in -Real.pi..Real.pi, H y) * E := by
        rw [intervalIntegral.integral_mul_const]
      _ ≤ (2 * Real.pi * rate) * E :=
        mul_le_mul_of_nonneg_right hHint hE
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hpi)]
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hpi]
  calc
    |∫ y in -Real.pi..Real.pi, H y * e y| ≤
        2 * Real.pi * rate * E := htotal
    _ = sixVertexRootDensityContractionRate c * E * (2 * Real.pi) := by
      dsimp [rate]
      ring

end

end StatMech.FrontierD
