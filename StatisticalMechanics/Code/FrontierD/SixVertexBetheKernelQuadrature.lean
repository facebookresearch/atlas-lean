/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexRootDensityKernelLipschitz









namespace StatMech.FrontierD

noncomputable section

theorem sixVertexRootDensityWeight_le
    {c : Real} (hc : 2 < c) (y : Real) :
    sixVertexRootDensityWeight c y <=
      (sixVertexAnisotropyMagnitude c + 1) /
        sixVertexRootDensityScale c := by
  exact div_le_div_of_nonneg_right
    (sixVertexBetheIntegratingFactor_bounds hc y).2
    (sixVertexRootDensityScale_pos hc).le

theorem sixVertexRootDensityWeight_lipschitz
    {c : Real} (hc : 2 < c) (y z : Real) :
    |sixVertexRootDensityWeight c y -
        sixVertexRootDensityWeight c z| <=
      (1 / sixVertexRootDensityScale c) * |y - z| := by
  have hs := sixVertexRootDensityScale_pos hc
  unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
  rw [div_sub_div_same]
  rw [abs_div, abs_of_pos hs]
  rw [div_le_iff₀ hs]
  have hcos := Real.abs_cos_sub_cos_le y z
  calc
    |(Real.cos y - sixVertexDelta c) -
        (Real.cos z - sixVertexDelta c)| =
        |Real.cos y - Real.cos z| := by ring_nf
    _ <= |y - z| := hcos
    _ = (1 / sixVertexRootDensityScale c) * |y - z| *
        sixVertexRootDensityScale c := by
      field_simp [hs.ne']

theorem sixVertexRootDensityKernel_div_weight_lipschitz
    {c : Real} (hc : 2 < c) (x y z : Real) :
    |sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y -
        sixVertexRootDensityKernel c x z /
          sixVertexRootDensityWeight c z| <=
      sixVertexThetaLeftKernelLipschitzBound c * |y - z| := by
  rw [sixVertexRootDensityKernel_div_weight hc,
    sixVertexRootDensityKernel_div_weight hc]
  have h := sixVertexThetaLeftKernel_lipschitz hc y z x
  rw [sixVertexThetaDerivativeDenominator_swap c x y,
    sixVertexThetaDerivativeDenominator_swap c x z] at h
  calc
    |-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y -
        -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x z| =
        |4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y -
        4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x z| := by
      rw [show
        -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
              sixVertexThetaDerivativeDenominator c x y -
            -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
              sixVertexThetaDerivativeDenominator c x z =
          -(4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
              sixVertexThetaDerivativeDenominator c x y -
            4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
              sixVertexThetaDerivativeDenominator c x z) by ring,
        abs_neg]
    _ <= _ := h

theorem abs_sixVertexRootDensityKernel_div_weight_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    |sixVertexRootDensityKernel c x y /
        sixVertexRootDensityWeight c y| <=
      sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1) := by
  rw [sixVertexRootDensityKernel_div_weight hc]
  rw [← Real.norm_eq_abs]
  exact norm_sixVertexTheta_rightDerivative_le hc x y



theorem abs_kernel_mul_finiteDensity_cellMass_sub_integral_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n <= N) (p : Fin n → Real) (x a b u mass : Real)
    (hab : a <= b) (hu : u ∈ Set.Icc a b)
    (hmass : ∫ y in a..b,
      sixVertexFiniteRootDensity c N n p y = mass) :
    |sixVertexRootDensityKernel c x u * mass -
        ∫ y in a..b,
          sixVertexRootDensityKernel c x y *
            sixVertexFiniteRootDensity c N n p y| <=
      sixVertexRootDensityKernelLipschitzBound c *
        sixVertexFiniteRootDensityUniformBound c * (b - a) ^ 2 := by
  let K0 := sixVertexRootDensityKernel c x u
  let rho := sixVertexFiniteRootDensity c N n p
  let L := sixVertexRootDensityKernelLipschitzBound c
  let U := sixVertexFiniteRootDensityUniformBound c
  have hgap : 0 <= b - a := sub_nonneg.mpr hab
  have hL : 0 <= L := (sixVertexRootDensityKernelLipschitzBound_pos hc).le
  have hU : 0 <= U := by
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    dsimp [U, sixVertexFiniteRootDensityUniformBound]
    positivity
  have hrho : Continuous rho :=
    continuous_sixVertexFiniteRootDensity hc N n p
  have hkernel : Continuous (sixVertexRootDensityKernel c x) := by
    unfold sixVertexRootDensityKernel sixVertexRootDensityScale
      sixVertexBetheIntegratingFactor sixVertexThetaDerivativeDenominator
      sixVertexThetaDenominator sixVertexAnisotropyMagnitude sixVertexDelta
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro y
      exact (mul_pos (sixVertexRootDensityScale_pos hc)
        (sixVertexThetaDerivativeDenominator_pos hc x y)).ne'
  have hrewrite :
      K0 * mass - ∫ y in a..b,
          sixVertexRootDensityKernel c x y * rho y =
        ∫ y in a..b,
          (K0 - sixVertexRootDensityKernel c x y) * rho y := by
    rw [← hmass]
    rw [show K0 * (∫ y in a..b, rho y) =
        ∫ y in a..b, K0 * rho y by
      rw [intervalIntegral.integral_const_mul]]
    have hconstCont : Continuous (fun y : Real => K0 * rho y) :=
      continuous_const.mul hrho
    have hprodCont : Continuous (fun y : Real =>
        sixVertexRootDensityKernel c x y * rho y) := hkernel.mul hrho
    have hsub := intervalIntegral.integral_sub (μ := MeasureTheory.volume)
      (hconstCont.intervalIntegrable a b)
      (hprodCont.intervalIntegrable a b)
    change (∫ y in a..b, K0 * rho y -
        sixVertexRootDensityKernel c x y * rho y) =
      (∫ y in a..b, K0 * rho y) -
        ∫ y in a..b,
          sixVertexRootDensityKernel c x y * rho y at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  change |K0 * mass - ∫ y in a..b,
      sixVertexRootDensityKernel c x y * rho y| <=
    L * U * (b - a) ^ 2
  rw [hrewrite]
  have hbound :
      ‖∫ y in a..b, (K0 - sixVertexRootDensityKernel c x y) * rho y‖ <=
        (L * (b - a) * U) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [Set.uIoc_of_le hab] at hy
    have hay : a <= y := hy.1.le
    have hyb : y <= b := hy.2
    have huy : |u - y| <= b - a := by
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
    have hKdiff :
        |K0 - sixVertexRootDensityKernel c x y| <= L * (b - a) := by
      exact (sixVertexRootDensityKernel_lipschitz_right hc x u y).trans
        (mul_le_mul_of_nonneg_left huy hL)
    have hrhoBound : |rho y| <= U :=
      abs_sixVertexFiniteRootDensity_le hc hN hn p y
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hKdiff hrhoBound (abs_nonneg _) (mul_nonneg hL hgap)
  rw [Real.norm_eq_abs, abs_of_nonneg hgap] at hbound
  nlinarith




theorem abs_kernel_div_width_sub_finiteDensity_cellIntegral_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n + 1 <= N) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (x : Real) (j : Fin n) :
    |sixVertexRootDensityKernel c x (p j.castSucc) / N -
        ∫ y in p j.castSucc..p j.succ,
          sixVertexRootDensityKernel c x y *
            sixVertexFiniteRootDensity c N (n + 1) p y| <=
      sixVertexRootDensityKernelLipschitzBound c *
        sixVertexFiniteRootDensityUniformBound c *
          (p j.succ - p j.castSucc) ^ 2 := by
  let a := p j.castSucc
  let b := p j.succ
  let K0 := sixVertexRootDensityKernel c x a
  let rho := sixVertexFiniteRootDensity c N (n + 1) p
  let L := sixVertexRootDensityKernelLipschitzBound c
  let U := sixVertexFiniteRootDensityUniformBound c
  have hab : a <= b := (hopen.1 (by simp)).le
  have hgap : 0 <= b - a := sub_nonneg.mpr hab
  have hL : 0 <= L := (sixVertexRootDensityKernelLipschitzBound_pos hc).le
  have hU : 0 <= U := by
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    dsimp [U, sixVertexFiniteRootDensityUniformBound]
    positivity
  have hrho : Continuous rho :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have hkernel : Continuous (sixVertexRootDensityKernel c x) := by
    unfold sixVertexRootDensityKernel sixVertexRootDensityScale
      sixVertexBetheIntegratingFactor sixVertexThetaDerivativeDenominator
      sixVertexThetaDenominator sixVertexAnisotropyMagnitude sixVertexDelta
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro y
      exact (mul_pos (sixVertexRootDensityScale_pos hc)
        (sixVertexThetaDerivativeDenominator_pos hc x y)).ne'
  have hmass : ∫ y in a..b, rho y = 1 / N := by
    exact intervalIntegral_sixVertexFiniteRootDensity_adjacent hc hN hsol j
  have hrewrite :
      K0 / N - ∫ y in a..b,
          sixVertexRootDensityKernel c x y * rho y =
        ∫ y in a..b,
          (K0 - sixVertexRootDensityKernel c x y) * rho y := by
    rw [show K0 / (N : Real) = K0 * (1 / (N : Real)) by ring,
      ← hmass]
    rw [show K0 * (∫ y in a..b, rho y) =
        ∫ y in a..b, K0 * rho y by
      rw [intervalIntegral.integral_const_mul]]
    have hconstCont : Continuous (fun y : Real => K0 * rho y) :=
      continuous_const.mul hrho
    have hprodCont : Continuous (fun y : Real =>
        sixVertexRootDensityKernel c x y * rho y) :=
      hkernel.mul hrho
    have hsub := intervalIntegral.integral_sub (μ := MeasureTheory.volume)
      (hconstCont.intervalIntegrable a b)
      (hprodCont.intervalIntegrable a b)
    change (∫ y in a..b, K0 * rho y -
        sixVertexRootDensityKernel c x y * rho y) =
      (∫ y in a..b, K0 * rho y) -
        ∫ y in a..b,
          sixVertexRootDensityKernel c x y * rho y at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  change |K0 / N - ∫ y in a..b,
      sixVertexRootDensityKernel c x y * rho y| <=
    L * U * (b - a) ^ 2
  rw [hrewrite]
  have hbound :
      ‖∫ y in a..b, (K0 - sixVertexRootDensityKernel c x y) * rho y‖ <=
        (L * (b - a) * U) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [Set.uIoc_of_le hab] at hy
    have hay : a <= y := hy.1.le
    have hyb : y <= b := hy.2
    have hdist : |a - y| <= b - a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hay)]
      linarith
    have hKdiff :
        |K0 - sixVertexRootDensityKernel c x y| <= L * (b - a) := by
      exact (sixVertexRootDensityKernel_lipschitz_right hc x a y).trans
        (mul_le_mul_of_nonneg_left hdist hL)
    have hrhoBound : |rho y| <= U := by
      exact abs_sixVertexFiniteRootDensity_le hc hN hn p y
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hKdiff hrhoBound (abs_nonneg _) (mul_nonneg hL hgap)
  rw [Real.norm_eq_abs, abs_of_nonneg hgap] at hbound
  nlinarith



theorem abs_kernel_div_width_sub_finiteDensity_rightCellIntegral_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n + 1 <= N) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (x : Real) (j : Fin n) :
    |sixVertexRootDensityKernel c x (p j.succ) / N -
        ∫ y in p j.castSucc..p j.succ,
          sixVertexRootDensityKernel c x y *
            sixVertexFiniteRootDensity c N (n + 1) p y| <=
      sixVertexRootDensityKernelLipschitzBound c *
        sixVertexFiniteRootDensityUniformBound c *
          (p j.succ - p j.castSucc) ^ 2 := by
  have hab : p j.castSucc <= p j.succ := (hopen.1 (by simp)).le
  have hu : p j.succ ∈ Set.Icc (p j.castSucc) (p j.succ) :=
    ⟨hab, le_rfl⟩
  have hmass := intervalIntegral_sixVertexFiniteRootDensity_adjacent
    hc hN hsol j
  have h := abs_kernel_mul_finiteDensity_cellMass_sub_integral_le
    hc hN hn p x (p j.castSucc) (p j.succ) (p j.succ)
      (1 / (N : Real)) hab hu hmass
  simpa [div_eq_mul_inv] using h



theorem abs_kernel_div_width_sub_finiteDensity_boundaryIntegral_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : N = 2 * (n + 1)) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (x : Real) :
    |sixVertexRootDensityKernel c x (p 0) / N -
        ∫ y in p (Fin.last n) - 2 * Real.pi..p 0,
          sixVertexRootDensityKernel c x y *
            sixVertexFiniteRootDensity c N (n + 1) p y| <=
      sixVertexRootDensityKernelLipschitzBound c *
        sixVertexFiniteRootDensityUniformBound c *
          (p 0 - (p (Fin.last n) - 2 * Real.pi)) ^ 2 := by
  let a := p (Fin.last n) - 2 * Real.pi
  have hn : n + 1 <= N := by omega
  have hab : a <= p 0 := by
    have hfirst := (hopen.2.2 (0 : Fin (n + 1))).1
    have hlast := (hopen.2.2 (Fin.last n)).2
    dsimp [a]
    linarith [Real.pi_pos]
  have hu : p 0 ∈ Set.Icc a (p 0) := ⟨hab, le_rfl⟩
  have hboundary := intervalIntegral_sixVertexFiniteRootDensity_boundary
    hc hN hsol
  have hmass :
      ∫ y in a..p 0, sixVertexFiniteRootDensity c N (n + 1) p y =
        1 / (N : Real) := by
    change (∫ y in p (Fin.last n) - 2 * Real.pi..p 0,
      sixVertexFiniteRootDensity c N (n + 1) p y) = _
    rw [hboundary]
    have hhalfReal : (N : Real) = 2 * (n + 1 : Real) := by
      exact_mod_cast hhalf
    rw [hhalfReal]
    ring
  have h := abs_kernel_mul_finiteDensity_cellMass_sub_integral_le
    hc hN hn p x a (p 0) (p 0) (1 / (N : Real)) hab hu hmass
  simpa [a, div_eq_mul_inv] using h

end

end StatMech.FrontierD
