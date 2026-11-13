/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailContinuumEquation









namespace StatMech.FrontierD

noncomputable section


def SixVertexSatisfiesContinuousDensityEquation
    (c : Real) (rho : Real -> Real) : Prop :=
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
    sixVertexRootDensityWeight c x * rho x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) *
          ∫ y in -Real.pi..Real.pi,
            sixVertexRootDensityKernel c x y * rho y



theorem sixVertexContinuousDensityEquation_unique_of_equal_mass
    {c : Real} (hc : 2 < c) {rho sigma : Real -> Real}
    (hrho : Continuous rho) (hsigma : Continuous sigma)
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hsigmaEq : SixVertexSatisfiesContinuousDensityEquation c sigma)
    (hmass : (∫ y in -Real.pi..Real.pi, rho y) =
      ∫ y in -Real.pi..Real.pi, sigma y) :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi, rho x = sigma x := by
  let e : Real -> Real := fun y =>
    sixVertexRootDensityWeight c y * (rho y - sigma y)
  have hweight : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have he : Continuous e := hweight.mul (hrho.sub hsigma)
  have hrhoInt : IntervalIntegrable rho MeasureTheory.volume
      (-Real.pi) Real.pi := hrho.intervalIntegrable _ _
  have hsigmaInt : IntervalIntegrable sigma MeasureTheory.volume
      (-Real.pi) Real.pi := hsigma.intervalIntegrable _ _
  have heMass :
      (∫ y in -Real.pi..Real.pi,
        e y / sixVertexRootDensityWeight c y) = 0 := by
    have heq : (fun y => e y / sixVertexRootDensityWeight c y) =
        fun y => rho y - sigma y := by
      funext y
      dsimp [e]
      field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
    rw [heq, intervalIntegral.integral_sub hrhoInt hsigmaInt, hmass,
      sub_self]
  have hnonempty : (Set.Icc (-Real.pi) Real.pi).Nonempty :=
    Set.nonempty_Icc.2 (by linarith [Real.pi_pos])
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn hnonempty
    he.abs.continuousOn
  let E := |e x0|
  have hE : 0 <= E := abs_nonneg _
  have hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| <= E :=
    fun y hy => hmax hy
  have hcontract := sixVertexRootDensityKernel_contraction hc he hE heMass
    hbound x0
  have hkernel (x : Real) : Continuous (sixVertexRootDensityKernel c x) :=
    (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
  have heqPoint (x : Real) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      e x = -(1 / (2 * Real.pi)) *
        ∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) * e y := by
    let IR := ∫ y in -Real.pi..Real.pi,
      sixVertexRootDensityKernel c x y * rho y
    let IS := ∫ y in -Real.pi..Real.pi,
      sixVertexRootDensityKernel c x y * sigma y
    have hRint : IntervalIntegrable
        (fun y => sixVertexRootDensityKernel c x y * rho y)
        MeasureTheory.volume (-Real.pi) Real.pi :=
      ((hkernel x).mul hrho).intervalIntegrable _ _
    have hSint : IntervalIntegrable
        (fun y => sixVertexRootDensityKernel c x y * sigma y)
        MeasureTheory.volume (-Real.pi) Real.pi :=
      ((hkernel x).mul hsigma).intervalIntegrable _ _
    have hJ :
        (∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) * e y) = IR - IS := by
      rw [show (fun y =>
          (sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) * e y) =
        fun y => sixVertexRootDensityKernel c x y *
          (rho y - sigma y) by
          funext y
          dsimp [e]
          field_simp [(sixVertexRootDensityWeight_pos hc y).ne']]
      rw [show (fun y => sixVertexRootDensityKernel c x y *
          (rho y - sigma y)) =
        fun y => sixVertexRootDensityKernel c x y * rho y -
          sixVertexRootDensityKernel c x y * sigma y by
          funext y
          ring]
      exact intervalIntegral.integral_sub hRint hSint
    have hR := hrhoEq x hx
    have hS := hsigmaEq x hx
    dsimp [e]
    rw [mul_sub, hR, hS, hJ]
    ring
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hEzero : E = 0 := by
    have hpoint := congrArg abs (heqPoint x0 hx0)
    have hle : E <= sixVertexRootDensityContractionRate c * E := by
      calc
        E = |e x0| := rfl
        _ = |-(1 / (2 * Real.pi)) *
            ∫ y in -Real.pi..Real.pi,
              (sixVertexRootDensityKernel c x0 y /
                sixVertexRootDensityWeight c y) * e y| := hpoint
        _ = |(1 / (2 * Real.pi)) *
            ∫ y in -Real.pi..Real.pi,
              (sixVertexRootDensityKernel c x0 y /
                sixVertexRootDensityWeight c y) * e y| := by
          rw [show -(1 / (2 * Real.pi)) *
              (∫ y in -Real.pi..Real.pi,
                (sixVertexRootDensityKernel c x0 y /
                  sixVertexRootDensityWeight c y) * e y) =
            -((1 / (2 * Real.pi)) *
              ∫ y in -Real.pi..Real.pi,
                (sixVertexRootDensityKernel c x0 y /
                  sixVertexRootDensityWeight c y) * e y) by ring,
            abs_neg]
        _ <= sixVertexRootDensityContractionRate c * E := hcontract
    nlinarith [hrate.2]
  intro x hx
  have hex : |e x| = 0 := le_antisymm
    ((hbound x hx).trans_eq hEzero) (abs_nonneg _)
  have hezero : e x = 0 := abs_eq_zero.mp hex
  dsimp [e] at hezero
  exact sub_eq_zero.mp (mul_eq_zero.mp hezero |>.resolve_left
    (sixVertexRootDensityWeight_pos hc x).ne')

end

end StatMech.FrontierD
