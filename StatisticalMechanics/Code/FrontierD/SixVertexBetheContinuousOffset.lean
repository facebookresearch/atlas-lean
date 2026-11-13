/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheContinuumUniqueness









namespace StatMech.FrontierD

noncomputable section


def sixVertexContinuousOffsetSource (c x : Real) : Real :=
  (sixVertexTheta c x (-Real.pi) + sixVertexTheta c x Real.pi) / 2



def sixVertexContinuousOffsetKernel (c x y : Real) : Real :=
  sixVertexRootDensityKernel c x y / sixVertexRootDensityWeight c y

theorem sixVertexContinuousOffsetKernel_eq_thetaRightDerivative
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexContinuousOffsetKernel c x y =
      deriv (fun t => sixVertexTheta c x t) y := by
  rw [(hasDerivAt_sixVertexTheta_right hc x y).deriv]
  exact sixVertexRootDensityKernel_div_weight hc x y

theorem continuous_sixVertexContinuousOffsetSource
    {c : Real} (hc : 2 < c) :
    Continuous (sixVertexContinuousOffsetSource c) := by
  unfold sixVertexContinuousOffsetSource
  have htheta := continuous_sixVertexTheta hc
  exact ((htheta.comp
    (continuous_id.prodMk continuous_const)).add
      (htheta.comp (continuous_id.prodMk continuous_const))).div_const 2

theorem odd_sixVertexContinuousOffsetSource (c : Real) :
    Function.Odd (sixVertexContinuousOffsetSource c) := by
  intro x
  unfold sixVertexContinuousOffsetSource
  have hnegPi := sixVertexTheta_neg c x Real.pi
  have hpi := sixVertexTheta_neg c x (-Real.pi)
  simp only [neg_neg] at hpi
  rw [hnegPi, hpi]
  ring

theorem sixVertexRootDensityWeight_neg (c x : Real) :
    sixVertexRootDensityWeight c (-x) =
      sixVertexRootDensityWeight c x := by
  simp [sixVertexRootDensityWeight, sixVertexBetheIntegratingFactor,
    Real.cos_neg]



def SixVertexSatisfiesContinuousOffsetEquation
    (c : Real) (tau : Real → Real) : Prop :=
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
    2 * Real.pi * tau x = sixVertexContinuousOffsetSource c x -
      ∫ y in -Real.pi..Real.pi,
        sixVertexContinuousOffsetKernel c x y * tau y

theorem intervalIntegral_neg_pi_pi_eq_zero_of_odd
    {f : Real → Real} (hf : Function.Odd f) :
    (∫ x in -Real.pi..Real.pi, f x) = 0 := by
  have hcomp := intervalIntegral.integral_comp_neg
    (f := f) (a := -Real.pi) (b := Real.pi)
  have hleft :
      (∫ x in -Real.pi..Real.pi, f (-x)) =
        -(∫ x in -Real.pi..Real.pi, f x) := by
    rw [show (fun x => f (-x)) = fun x => -f x by
      funext x
      exact hf x]
    rw [intervalIntegral.integral_neg]
  have hright :
      (∫ x in -Real.pi..Real.pi, f (-x)) =
        ∫ x in -Real.pi..Real.pi, f x := by
    simpa only [neg_neg] using hcomp
  linarith




theorem sixVertexContinuousOffsetEquation_unique_of_odd
    {c : Real} (hc : 2 < c) {tau sigma : Real → Real}
    (htau : Continuous tau) (hsigma : Continuous sigma)
    (htauOdd : Function.Odd tau) (hsigmaOdd : Function.Odd sigma)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    (hsigmaEq : SixVertexSatisfiesContinuousOffsetEquation c sigma) :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi, tau x = sigma x := by
  let e : Real → Real := fun y => tau y - sigma y
  have he : Continuous e := htau.sub hsigma
  have heOdd : Function.Odd e := by
    intro y
    dsimp [e]
    rw [htauOdd y, hsigmaOdd y]
    ring
  have hweight : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have heQuotOdd : Function.Odd
      (fun y => e y / sixVertexRootDensityWeight c y) := by
    intro y
    dsimp only
    rw [heOdd y, sixVertexRootDensityWeight_neg]
    ring
  have heMass :
      (∫ y in -Real.pi..Real.pi,
        e y / sixVertexRootDensityWeight c y) = 0 :=
    intervalIntegral_neg_pi_pi_eq_zero_of_odd heQuotOdd
  have hnonempty : (Set.Icc (-Real.pi) Real.pi).Nonempty :=
    Set.nonempty_Icc.2 (by linarith [Real.pi_pos])
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn hnonempty
    he.abs.continuousOn
  let E := |e x0|
  have hE : 0 ≤ E := abs_nonneg _
  have hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| ≤ E :=
    fun y hy => hmax hy
  have hcontract := sixVertexRootDensityKernel_contraction hc he hE heMass
    hbound x0
  have hkernel (x : Real) : Continuous
      (sixVertexContinuousOffsetKernel c x) := by
    unfold sixVertexContinuousOffsetKernel
    exact (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous.div
      hweight (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
  have heqPoint (x : Real) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      e x = -(1 / (2 * Real.pi)) *
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * e y := by
    let IT := ∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c x y * tau y
    let IS := ∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c x y * sigma y
    have hTint : IntervalIntegrable
        (fun y => sixVertexContinuousOffsetKernel c x y * tau y)
        MeasureTheory.volume (-Real.pi) Real.pi :=
      ((hkernel x).mul htau).intervalIntegrable _ _
    have hSint : IntervalIntegrable
        (fun y => sixVertexContinuousOffsetKernel c x y * sigma y)
        MeasureTheory.volume (-Real.pi) Real.pi :=
      ((hkernel x).mul hsigma).intervalIntegrable _ _
    have hJ :
        (∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * e y) = IT - IS := by
      rw [show (fun y => sixVertexContinuousOffsetKernel c x y * e y) =
        fun y => sixVertexContinuousOffsetKernel c x y * tau y -
          sixVertexContinuousOffsetKernel c x y * sigma y by
          funext y
          dsimp [e]
          ring]
      exact intervalIntegral.integral_sub hTint hSint
    have hT := htauEq x hx
    have hS := hsigmaEq x hx
    dsimp [e]
    rw [hJ]
    change 2 * Real.pi * tau x =
      sixVertexContinuousOffsetSource c x - IT at hT
    change 2 * Real.pi * sigma x =
      sixVertexContinuousOffsetSource c x - IS at hS
    field_simp [Real.pi_ne_zero]
    linarith
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hEzero : E = 0 := by
    have hpoint := congrArg abs (heqPoint x0 hx0)
    have hle : E ≤ sixVertexRootDensityContractionRate c * E := by
      calc
        E = |e x0| := rfl
        _ = |-(1 / (2 * Real.pi)) *
            ∫ y in -Real.pi..Real.pi,
              sixVertexContinuousOffsetKernel c x0 y * e y| := hpoint
        _ = |(1 / (2 * Real.pi)) *
            ∫ y in -Real.pi..Real.pi,
              (sixVertexRootDensityKernel c x0 y /
                sixVertexRootDensityWeight c y) * e y| := by
          rw [show -(1 / (2 * Real.pi)) *
              (∫ y in -Real.pi..Real.pi,
                sixVertexContinuousOffsetKernel c x0 y * e y) =
            -((1 / (2 * Real.pi)) *
              ∫ y in -Real.pi..Real.pi,
                (sixVertexRootDensityKernel c x0 y /
                  sixVertexRootDensityWeight c y) * e y) by
              unfold sixVertexContinuousOffsetKernel
              ring,
            abs_neg]
        _ ≤ sixVertexRootDensityContractionRate c * E := hcontract
    nlinarith [hrate.2]
  intro x hx
  have hex : |e x| = 0 := le_antisymm
    ((hbound x hx).trans_eq hEzero) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hex)

end

end StatMech.FrontierD
