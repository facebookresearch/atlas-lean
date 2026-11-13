/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFixedChargePeriodicQuadrature
import Code.FrontierD.SixVertexBetheOffsetTaylor
import Code.FrontierD.SixVertexBetheContinuousOffset





namespace StatMech.FrontierD

noncomputable section

theorem periodic_sixVertexRootDensityWeight (c : Real) :
    Function.Periodic (sixVertexRootDensityWeight c) (2 * Real.pi) := by
  intro x
  unfold sixVertexRootDensityWeight
  rw [sixVertexBetheIntegratingFactor_add_two_pi]

theorem periodic_sixVertexContinuousOffsetKernel_right (c x : Real) :
    Function.Periodic (sixVertexContinuousOffsetKernel c x)
      (2 * Real.pi) :=
  (periodic_sixVertexRootDensityKernel_right c x).div
    (periodic_sixVertexRootDensityWeight c)

def sixVertexOffsetQuotientLipschitzBound
    (c lower G D : Real) : Real :=
  (sixVertexThetaLeftKernelLipschitzBound c * G +
      (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * D) / lower +
    (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1)) * G *
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) / lower ^ 2

def sixVertexOffsetQuotientLipschitzNNReal
    (c lower G D : Real) : NNReal :=
  Real.toNNReal (sixVertexOffsetQuotientLipschitzBound c lower G D)

theorem lipschitzWith_sixVertexContinuousOffsetKernel_mul_div_finiteDensity
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) (hn : n ≤ N)
    (p : Fin n → Real) {lower G : Real} (hlower : 0 < lower)
    (hdensity : ∀ y, lower ≤ sixVertexFiniteRootDensity c N n p y)
    {tau : Real → Real} {D : NNReal}
    (htauLip : LipschitzWith D tau) (htauBound : ∀ y, |tau y| ≤ G)
    (x : Real) :
    LipschitzWith (sixVertexOffsetQuotientLipschitzNNReal c lower G D)
      (fun y => sixVertexContinuousOffsetKernel c x y * tau y /
        sixVertexFiniteRootDensity c N n p y) := by
  let K : Real → Real := sixVertexContinuousOffsetKernel c x
  let rho := sixVertexFiniteRootDensity c N n p
  let A := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  let LK := sixVertexThetaLeftKernelLipschitzBound c
  let LR : Real := sixVertexFiniteRootDensityLipschitzConstant c
  let C := sixVertexOffsetQuotientLipschitzBound c lower G D
  have hG : 0 ≤ G := (abs_nonneg (tau 0)).trans (htauBound 0)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hLK : 0 ≤ LK := (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
  have hLR : 0 ≤ LR := by dsimp [LR]; exact NNReal.coe_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C, sixVertexOffsetQuotientLipschitzBound]
    positivity
  have hcoe : (sixVertexOffsetQuotientLipschitzNNReal c lower G D : Real) = C := by
    exact Real.coe_toNNReal _ hC
  have hKLip : LipschitzWith (sixVertexThetaDerivativeLipschitzNNReal c) K := by
    have heq : K = fun y =>
        -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y := by
      funext y
      exact sixVertexRootDensityKernel_div_weight hc x y
    rw [heq]
    exact lipschitzWith_sixVertexThetaRightDerivative hc x
  have hrhoLip := lipschitzWith_sixVertexFiniteRootDensity hc hN hn p
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, Real.dist_eq, hcoe]
  let dyz := |y - z|
  have hKdiff : |K y - K z| ≤ LK * dyz := by
    have h := hKLip.dist_le_mul y z
    rw [Real.dist_eq, Real.dist_eq,
      coe_sixVertexThetaDerivativeLipschitzNNReal hc] at h
    exact h
  have htaudiff : |tau y - tau z| ≤ (D : Real) * dyz := by
    simpa [Real.dist_eq] using htauLip.dist_le_mul y z
  have hrhodiff : |rho z - rho y| ≤ LR * dyz := by
    have h := hrhoLip.dist_le_mul z y
    simpa only [Real.dist_eq, rho, LR, dyz, abs_sub_comm] using h
  have hKy : |K y| ≤ A := by
    simpa [K, A, sixVertexContinuousOffsetKernel] using
      abs_sixVertexRootDensityKernel_div_weight_le hc x y
  have hKz : |K z| ≤ A := by
    simpa [K, A, sixVertexContinuousOffsetKernel] using
      abs_sixVertexRootDensityKernel_div_weight_le hc x z
  have hry : 0 < rho y := hlower.trans_le (hdensity y)
  have hrz : 0 < rho z := hlower.trans_le (hdensity z)
  have hrearrange :
      K y * tau y / rho y - K z * tau z / rho z =
        (K y - K z) * tau y / rho y +
        K z * (tau y - tau z) / rho y +
        K z * tau z * (rho z - rho y) / (rho y * rho z) := by
    field_simp [hry.ne', hrz.ne']
    ring
  rw [hrearrange]
  calc
    |(K y - K z) * tau y / rho y +
        K z * (tau y - tau z) / rho y +
        K z * tau z * (rho z - rho y) / (rho y * rho z)| ≤
      |(K y - K z) * tau y / rho y| +
        |K z * (tau y - tau z) / rho y| +
        |K z * tau z * (rho z - rho y) / (rho y * rho z)| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (LK * dyz * G) / lower +
        (A * ((D : Real) * dyz)) / lower +
        (A * G * (LR * dyz)) / (lower ^ 2) := by
      rw [abs_div, abs_div, abs_div, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_mul, abs_of_pos hry, abs_of_pos hrz]
      apply add_le_add
      · apply add_le_add
        · have hnum := mul_le_mul hKdiff (htauBound y)
            (abs_nonneg (tau y)) (mul_nonneg hLK (abs_nonneg _))
          calc
            |K y - K z| * |tau y| / rho y ≤
                (LK * dyz * G) / rho y :=
              div_le_div_of_nonneg_right hnum hry.le
            _ ≤ (LK * dyz * G) / lower :=
              div_le_div_of_nonneg_left
                (mul_nonneg (mul_nonneg hLK (abs_nonneg _)) hG)
                hlower (hdensity y)
        · have hnum := mul_le_mul hKz htaudiff
            (abs_nonneg (tau y - tau z)) hA
          calc
            |K z| * |tau y - tau z| / rho y ≤
                (A * ((D : Real) * dyz)) / rho y :=
              div_le_div_of_nonneg_right hnum hry.le
            _ ≤ (A * ((D : Real) * dyz)) / lower :=
              div_le_div_of_nonneg_left
                (mul_nonneg hA (mul_nonneg (NNReal.coe_nonneg D) (abs_nonneg _)))
                hlower (hdensity y)
      · have hnum : |K z| * |tau z| * |rho z - rho y| ≤
            A * G * (LR * dyz) := by
          exact mul_le_mul
            (mul_le_mul hKz (htauBound z) (abs_nonneg _) hA)
            hrhodiff (abs_nonneg _) (mul_nonneg hA hG)
        have hden : lower ^ 2 ≤ rho y * rho z := by
          simpa [pow_two] using
            mul_le_mul (hdensity y) (hdensity z) hlower.le hry.le
        calc
          |K z| * |tau z| * |rho z - rho y| / (rho y * rho z) ≤
              (A * G * (LR * dyz)) / (rho y * rho z) :=
            div_le_div_of_nonneg_right hnum (mul_pos hry hrz).le
          _ ≤ (A * G * (LR * dyz)) / lower ^ 2 :=
            div_le_div_of_nonneg_left
              (mul_nonneg (mul_nonneg hA hG) (mul_nonneg hLR (abs_nonneg _)))
              (sq_pos_of_pos hlower) hden
    _ = C * dyz := by
      dsimp [C, sixVertexOffsetQuotientLipschitzBound, A, LK, LR, dyz]
      field_simp [hlower.ne']




theorem abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ y,
      lower ≤ sixVertexFiniteRootDensity c N (n + 1) p y)
    (x : Real)
    {tau : Real → Real} {C : NNReal} {G : Real}
    (htau : Continuous tau)
    (htauPeriodic : Function.Periodic tau (2 * Real.pi))
    (htauBound : ∀ y, |tau y| ≤ G)
    (hlip : LipschitzWith C (fun y =>
      sixVertexContinuousOffsetKernel c x y * tau y /
        sixVertexFiniteRootDensity c N (n + 1) p y)) :
    |(∑ j, sixVertexContinuousOffsetKernel c x (p j) * tau (p j) /
          sixVertexFiniteRootDensity c N (n + 1) p (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * tau y| ≤
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
          ((2 * (r : Real) + 1) / ((N : Real) * lower)) *
            (2 * Real.pi) +
        (2 * (r : Real) / N) *
          ((sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1)) * G / lower) := by
  let rhoN := sixVertexFiniteRootDensity c N (n + 1) p
  let f : Real → Real := fun y =>
    sixVertexContinuousOffsetKernel c x y * tau y / rhoN y
  have hrho : Continuous rhoN :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have hkernel : Continuous (sixVertexContinuousOffsetKernel c x) := by
    unfold sixVertexContinuousOffsetKernel
    exact (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous.div
      (by
        unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
          sixVertexRootDensityScale
        fun_prop)
      (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
  have hf : Continuous f :=
    (hkernel.mul htau).div hrho
      (fun y => (hlower.trans_le (hdensity y)).ne')
  have hfPeriodic : Function.Periodic f (2 * Real.pi) :=
    ((periodic_sixVertexContinuousOffsetKernel_right c x).mul
      htauPeriodic).div
        (periodic_sixVertexFiniteRootDensity c N (n + 1) p)
  have hfBound : ∀ y, |f y| ≤
      (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * G / lower := by
    intro y
    have hkernelBound := abs_sixVertexRootDensityKernel_div_weight_le hc x y
    have hrhoLower := hdensity y
    have hrhoPos : 0 < rhoN y := hlower.trans_le hrhoLower
    dsimp [f]
    rw [abs_div, abs_mul, abs_of_pos hrhoPos]
    have hprod := mul_le_mul hkernelBound (htauBound y)
      (abs_nonneg _) (by
        have hd := one_lt_sixVertexAnisotropyMagnitude hc
        positivity : 0 ≤ sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1))
    have hG : 0 ≤ G := (abs_nonneg (tau 0)).trans (htauBound 0)
    have hratio : 0 ≤ sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1) := by
      have hd := one_lt_sixVertexAnisotropyMagnitude hc
      positivity
    calc
      |sixVertexContinuousOffsetKernel c x y| * |tau y| / rhoN y ≤
          ((sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1)) * G) / rhoN y :=
        div_le_div_of_nonneg_right hprod hrhoPos.le
      _ ≤ ((sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1)) * G) / lower :=
        div_le_div_of_nonneg_left (mul_nonneg hratio hG) hlower hrhoLower
  have hquad :=
    abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_fixedCharge
      hc hN hcharge hopen hsol hlower hdensity hf hlip hfPeriodic hfBound
  change |(∑ j, f (p j)) / N -
      ∫ y in -Real.pi..Real.pi, f y * rhoN y| ≤ _ at hquad
  have hintegral :
      (∫ y in -Real.pi..Real.pi, f y * rhoN y) =
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * tau y := by
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [f, rhoN]
    field_simp [(hlower.trans_le (hdensity y)).ne']
  rw [hintegral] at hquad
  exact hquad



theorem abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_of_lipschitz
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ y,
      lower ≤ sixVertexFiniteRootDensity c N (n + 1) p y)
    (x : Real) {tau : Real → Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauPeriodic : Function.Periodic tau (2 * Real.pi))
    (htauBound : ∀ y, |tau y| ≤ G) :
    |(∑ j, sixVertexContinuousOffsetKernel c x (p j) * tau (p j) /
          sixVertexFiniteRootDensity c N (n + 1) p (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * tau y| ≤
      (sixVertexOffsetQuotientLipschitzNNReal c lower G D : Real) *
          sixVertexFiniteRootDensityUniformBound c *
          ((2 * (r : Real) + 1) / ((N : Real) * lower)) *
            (2 * Real.pi) +
        (2 * (r : Real) / N) *
          ((sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1)) * G / lower) := by
  apply abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge
    hc hN hcharge hopen hsol hlower hdensity x
    htauLip.continuous htauPeriodic htauBound
  exact lipschitzWith_sixVertexContinuousOffsetKernel_mul_div_finiteDensity
    hc hN (by omega) p hlower hdensity htauLip htauBound x

end

end StatMech.FrontierD
