/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheContinuousOffsetFourier
import Code.FrontierD.SixVertexBetheContinuousOffset
import Mathlib.Analysis.Calculus.SmoothSeries









namespace StatMech.FrontierD

open Filter Topology

noncomputable section


def sixVertexOffsetSourceCorrectionTerm
    (lam : Real) (n : Nat) (alpha : Real) : Real :=
  -2 * (-1 : Real) ^ (n + 1) *
      Real.exp (-2 * ((n + 1 : Real) * lam)) / (n + 1 : Real) *
    Real.sin ((n + 1 : Real) * alpha)


def sixVertexOffsetSourceRapidityProfile (lam alpha : Real) : Real :=
  -alpha + ∑' n : Nat, sixVertexOffsetSourceCorrectionTerm lam n alpha

def sixVertexOffsetSourceCorrectionDerivativeTerm
    (lam : Real) (n : Nat) (alpha : Real) : Real :=
  -2 * (-1 : Real) ^ (n + 1) *
    Real.exp (-2 * ((n + 1 : Real) * lam)) *
      Real.cos ((n + 1 : Real) * alpha)

theorem norm_sixVertexOffsetSourceCorrectionTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexOffsetSourceCorrectionTerm lam n alpha‖ <=
      2 * Real.exp (-2 * lam) ^ (n + 1) := by
  rw [sixVertexOffsetSourceCorrectionTerm, Real.norm_eq_abs, abs_mul, abs_div,
    abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : Real) <= 2),
    abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity : (0 : Real) < (n + 1 : Real)), mul_one]
  have hsin : |Real.sin ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  calc
    2 * Real.exp (-2 * ((n + 1 : Real) * lam)) /
          (n + 1 : Real) * |Real.sin ((n + 1 : Real) * alpha)| <=
        2 * Real.exp (-2 * ((n + 1 : Real) * lam)) := by
      have hn : 1 <= (n + 1 : Real) := by norm_num
      have hdiv : 2 * Real.exp (-2 * ((n + 1 : Real) * lam)) /
          (n + 1 : Real) <=
          2 * Real.exp (-2 * ((n + 1 : Real) * lam)) := by
        exact div_le_self (by positivity) hn
      nlinarith [mul_le_mul_of_nonneg_left hsin
        (by positivity : 0 <=
          2 * Real.exp (-2 * ((n + 1 : Real) * lam)) /
            (n + 1 : Real))]
    _ = 2 * Real.exp (-2 * lam) ^ (n + 1) := by
      rw [<- Real.exp_nat_mul]
      congr 2
      push_cast
      ring

theorem summable_sixVertexOffsetSourceCorrectionTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexOffsetSourceCorrectionTerm lam n alpha) := by
  have hq0 : 0 <= Real.exp (-2 * lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmajor : Summable (fun n : Nat =>
      2 * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left 2
  exact hmajor.of_norm_bounded
    (fun n => norm_sixVertexOffsetSourceCorrectionTerm_le lam n alpha)

theorem continuous_sixVertexOffsetSourceRapidityProfile
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexOffsetSourceRapidityProfile lam) := by
  unfold sixVertexOffsetSourceRapidityProfile
  apply Continuous.add (by fun_prop)
  apply continuous_tsum
  · intro n
    unfold sixVertexOffsetSourceCorrectionTerm
    fun_prop
  · exact (summable_sixVertexFourierRootDensityMajorant (by linarith :
      0 < 2 * lam))
  · intro n alpha
    simpa [sixVertexFourierRootDensityMajorant] using
      norm_sixVertexOffsetSourceCorrectionTerm_le lam n alpha

theorem hasDerivAt_sixVertexOffsetSourceCorrectionTerm
    (lam : Real) (n : Nat) (alpha : Real) :
    HasDerivAt (sixVertexOffsetSourceCorrectionTerm lam n)
      (sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) alpha := by
  unfold sixVertexOffsetSourceCorrectionTerm
    sixVertexOffsetSourceCorrectionDerivativeTerm
  have hsin : HasDerivAt
      (fun x : Real => Real.sin ((n + 1 : Real) * x))
      ((n + 1 : Real) * Real.cos ((n + 1 : Real) * alpha)) alpha := by
    convert Real.hasDerivAt_sin ((n + 1 : Real) * alpha) |>.comp alpha
      ((hasDerivAt_id alpha).const_mul (n + 1 : Real)) using 1 <;> ring
  convert hsin.const_mul
    (-2 * (-1 : Real) ^ (n + 1) *
      Real.exp (-2 * ((n + 1 : Real) * lam)) / (n + 1 : Real)) using 1
  field_simp [show (n + 1 : Real) ≠ 0 by positivity] <;> ring

theorem norm_sixVertexOffsetSourceCorrectionDerivativeTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha‖ <=
      sixVertexFourierRootDensityMajorant (2 * lam) n := by
  unfold sixVertexOffsetSourceCorrectionDerivativeTerm
    sixVertexFourierRootDensityMajorant
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : Real) <= 2), abs_pow, abs_neg,
    abs_one, one_pow, abs_of_pos (Real.exp_pos _)]
  have hcos : |Real.cos ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hexp :
      Real.exp (-2 * ((n + 1 : Real) * lam)) =
        Real.exp (-2 * lam) ^ (n + 1) := by
    rw [<- Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  calc
    2 * 1 * Real.exp (-2 * lam) ^ (n + 1) *
        |Real.cos ((n + 1 : Real) * alpha)| <=
      (2 * 1 * Real.exp (-2 * lam) ^ (n + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
    _ = 2 * Real.exp (-(2 * lam)) ^ (n + 1) := by ring

theorem hasDerivAt_sixVertexOffsetSourceRapidityProfile
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexOffsetSourceRapidityProfile lam)
      (-1 + ∑' n : Nat,
        sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) alpha := by
  have hseries : HasDerivAt
      (fun x => ∑' n : Nat, sixVertexOffsetSourceCorrectionTerm lam n x)
      (∑' n : Nat,
        sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) alpha := by
    apply hasDerivAt_tsum
      (u := sixVertexFourierRootDensityMajorant (2 * lam))
      (g' := sixVertexOffsetSourceCorrectionDerivativeTerm lam)
      (y₀ := 0)
    · exact summable_sixVertexFourierRootDensityMajorant (by linarith)
    · intro n x
      exact hasDerivAt_sixVertexOffsetSourceCorrectionTerm lam n x
    · intro n x
      exact norm_sixVertexOffsetSourceCorrectionDerivativeTerm_le lam n x
    · simpa [sixVertexOffsetSourceCorrectionTerm] using
        (summable_zero : Summable (fun _n : Nat => (0 : Real)))
  unfold sixVertexOffsetSourceRapidityProfile
  convert (hasDerivAt_id alpha).neg.add hseries using 1 <;> ring

theorem sixVertexOffsetSourceCorrectionDerivativeTerm_eq
    (lam : Real) (n : Nat) (alpha : Real) :
    sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha =
      -sixVertexXiFourierTerm (2 * lam) n (alpha - Real.pi) := by
  unfold sixVertexOffsetSourceCorrectionDerivativeTerm
    sixVertexXiFourierTerm
  have hcast : (n + 1 : Real) = ((n + 1 : Nat) : Real) := by norm_num
  rw [hcast, mul_sub, Real.cos_sub, Real.cos_nat_mul_pi,
    Real.sin_nat_mul_pi]
  push_cast
  ring

theorem sixVertexXiFourier_add_pi_eq_sub_pi
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexXiFourier lam (alpha + Real.pi) =
      sixVertexXiFourier lam (alpha - Real.pi) := by
  rw [sixVertexXiFourier_eq hlam, sixVertexXiFourier_eq hlam]
  congr 2
  rw [show alpha + Real.pi = (alpha - Real.pi) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

theorem hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq_Xi
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexOffsetSourceRapidityProfile lam)
      (-sixVertexXiFourier (2 * lam) (alpha - Real.pi)) alpha := by
  have h := hasDerivAt_sixVertexOffsetSourceRapidityProfile hlam alpha
  convert h using 1
  unfold sixVertexXiFourier
  rw [show (∑' n : Nat,
      sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) =
      -(∑' n : Nat,
        sixVertexXiFourierTerm (2 * lam) n (alpha - Real.pi)) by
    rw [<- tsum_neg]
    apply tsum_congr
    intro n
    exact sixVertexOffsetSourceCorrectionDerivativeTerm_eq lam n alpha]
  ring

theorem hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum
    {c : Real} (hc : 2 < c) (alpha : Real) :
    HasDerivAt
      (fun t => sixVertexContinuousOffsetSource c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) t))
      (-(sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c)
          (alpha + Real.pi) +
        sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c)
          (alpha - Real.pi)) / 2) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let k := sixVertexRapidityMomentum lam
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hk := hasDerivAt_sixVertexRapidityMomentum hlam alpha
  have hthetaLeft : HasDerivAt (fun x => sixVertexTheta c x (-Real.pi))
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-Real.pi) /
        sixVertexThetaDerivativeDenominator c (k alpha) (-Real.pi)) (k alpha) := by
    simpa [sixVertexBetheIntegratingFactor,
      sixVertexThetaDerivativeDenominator] using
      hasDerivAt_sixVertexTheta_left hc (k alpha) (-Real.pi)
  have hthetaRight : HasDerivAt (fun x => sixVertexTheta c x Real.pi)
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c Real.pi /
        sixVertexThetaDerivativeDenominator c (k alpha) Real.pi) (k alpha) := by
    simpa [sixVertexBetheIntegratingFactor,
      sixVertexThetaDerivativeDenominator] using
      hasDerivAt_sixVertexTheta_left hc (k alpha) Real.pi
  have hleft := hthetaLeft.comp alpha hk
  have hright := hthetaRight.comp alpha hk
  have hweight : sixVertexXiFourier lam alpha =
      sixVertexRootDensityWeight c (k alpha) := by
    exact (sixVertexRootDensityWeight_rapidityMomentum hc alpha).symm
  have hnegPi : -Real.pi = k (-Real.pi) := by
    exact (sixVertexRapidityMomentum_neg_pi hlam).symm
  have hpi : Real.pi = k Real.pi := by
    exact (sixVertexRapidityMomentum_pi hlam).symm
  have hleftDeriv :
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-Real.pi) /
          sixVertexThetaDerivativeDenominator c (k alpha) (-Real.pi)) *
          sixVertexXiFourier lam alpha =
        -sixVertexXiFourier (2 * lam) (alpha + Real.pi) := by
    have hkernel := sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative
      hc (k alpha) (-Real.pi)
    have hkernelRapid : sixVertexRootDensityKernel c (k alpha) (-Real.pi) =
        sixVertexXiFourier (2 * lam) (alpha - (-Real.pi)) := by
      calc
        _ = sixVertexRootDensityKernel c (k alpha) (k (-Real.pi)) :=
          congrArg (sixVertexRootDensityKernel c (k alpha)) hnegPi
        _ = _ := sixVertexRootDensityKernel_rapidityMomentum hc alpha (-Real.pi)
    rw [hweight]
    calc
      _ = -sixVertexRootDensityKernel c (k alpha) (-Real.pi) := by
        rw [hkernel]
        ring
      _ = -sixVertexXiFourier (2 * lam) (alpha - (-Real.pi)) := by
        rw [hkernelRapid]
      _ = _ := by ring_nf
  have hrightDeriv :
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c Real.pi /
          sixVertexThetaDerivativeDenominator c (k alpha) Real.pi) *
          sixVertexXiFourier lam alpha =
        -sixVertexXiFourier (2 * lam) (alpha - Real.pi) := by
    have hkernel := sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative
      hc (k alpha) Real.pi
    have hkernelRapid : sixVertexRootDensityKernel c (k alpha) Real.pi =
        sixVertexXiFourier (2 * lam) (alpha - Real.pi) := by
      calc
        _ = sixVertexRootDensityKernel c (k alpha) (k Real.pi) :=
          congrArg (sixVertexRootDensityKernel c (k alpha)) hpi
        _ = _ := sixVertexRootDensityKernel_rapidityMomentum hc alpha Real.pi
    rw [hweight]
    calc
      _ = -sixVertexRootDensityKernel c (k alpha) Real.pi := by
        rw [hkernel]
        ring
      _ = _ := by rw [hkernelRapid]
  unfold sixVertexContinuousOffsetSource
  convert hleft.add hright |>.div_const 2 using 1 <;>
    dsimp only [k, lam] <;>
    rw [hleftDeriv, hrightDeriv] <;>
    ring

theorem hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq_Xi
    {c : Real} (hc : 2 < c) (alpha : Real) :
    HasDerivAt
      (fun t => sixVertexContinuousOffsetSource c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) t))
      (-sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c)
        (alpha - Real.pi)) alpha := by
  have h := hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum
    hc alpha
  convert h using 1
  rw [sixVertexXiFourier_add_pi_eq_sub_pi
    (by linarith [sixVertexAntiferroelectricLambda_pos hc] :
      0 < 2 * sixVertexAntiferroelectricLambda c) alpha]
  ring



theorem sixVertexContinuousOffsetSource_rapidityMomentum
    {c : Real} (hc : 2 < c) (alpha : Real) :
    sixVertexContinuousOffsetSource c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) =
      sixVertexOffsetSourceRapidityProfile
        (sixVertexAntiferroelectricLambda c) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let f : Real -> Real := fun t =>
    sixVertexContinuousOffsetSource c (sixVertexRapidityMomentum lam t)
  let g : Real -> Real := sixVertexOffsetSourceRapidityProfile lam
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hf : Differentiable Real f := by
    intro t
    exact (hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq_Xi
      hc t).differentiableAt
  have hg : Differentiable Real g := by
    intro t
    exact (hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq_Xi hlam t)
      |>.differentiableAt
  have hderiv (t : Real) : fderiv Real f t = fderiv Real g t := by
    rw [(hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq_Xi
      hc t).hasFDerivAt.fderiv,
      (hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq_Xi hlam t)
        |>.hasFDerivAt.fderiv]
  have hfzero : f 0 = 0 := by
    have hodd := odd_sixVertexContinuousOffsetSource c 0
    have hkzero : sixVertexRapidityMomentum lam 0 = 0 := by
      simp [sixVertexRapidityMomentum]
    dsimp [f]
    rw [hkzero]
    have hodd' : sixVertexContinuousOffsetSource c 0 =
        -sixVertexContinuousOffsetSource c 0 := by
      simpa only [neg_zero] using hodd
    linarith
  have hgzero : g 0 = 0 := by
    simp [g, sixVertexOffsetSourceRapidityProfile,
      sixVertexOffsetSourceCorrectionTerm]
  have hfg : f = g := eq_of_fderiv_eq hf hg hderiv 0 (hfzero.trans hgzero.symm)
  exact congrFun hfg alpha


def sixVertexOffsetConvolutionTerm
    (lam : Real) (n : Nat) (alpha : Real) : Real :=
  2 * Real.exp (-2 * ((n + 1 : Real) * lam)) *
    ((-1 : Real) ^ (n + 1) *
      Real.tanh ((n + 1 : Real) * lam) / (n + 1 : Real)) *
    Real.sin ((n + 1 : Real) * alpha)

theorem norm_sixVertexOffsetConvolutionTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexOffsetConvolutionTerm lam n alpha‖ <=
      2 * Real.exp (-2 * lam) ^ (n + 1) := by
  unfold sixVertexOffsetConvolutionTerm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_div, abs_mul,
    abs_of_nonneg (by positivity : (0 : Real) <= 2),
    abs_of_pos (Real.exp_pos _), abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity : (0 : Real) < (n + 1 : Real))]
  have htanh : |Real.tanh ((n + 1 : Real) * lam)| <= 1 :=
    (Real.abs_tanh_lt_one _).le
  have hsin : |Real.sin ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hfrac : |Real.tanh ((n + 1 : Real) * lam)| /
      (n + 1 : Real) <= 1 := by
    have hn : 1 <= (n + 1 : Real) := by norm_num
    exact (div_le_one (by positivity)).2 (htanh.trans hn)
  have hprod :
      (|Real.tanh ((n + 1 : Real) * lam)| / (n + 1 : Real)) *
          |Real.sin ((n + 1 : Real) * alpha)| <= 1 := by
    nlinarith [mul_le_mul hfrac hsin (abs_nonneg _) (by positivity : (0 : Real) <= 1)]
  have hexp :
      Real.exp (-2 * ((n + 1 : Real) * lam)) =
        Real.exp (-2 * lam) ^ (n + 1) := by
    rw [<- Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  calc
    2 * Real.exp (-2 * lam) ^ (n + 1) *
          (1 * |Real.tanh ((n + 1 : Real) * lam)| / (n + 1 : Real)) *
          |Real.sin ((n + 1 : Real) * alpha)| =
        (2 * Real.exp (-2 * lam) ^ (n + 1)) *
          ((|Real.tanh ((n + 1 : Real) * lam)| / (n + 1 : Real)) *
            |Real.sin ((n + 1 : Real) * alpha)|) := by ring
    _ <= (2 * Real.exp (-2 * lam) ^ (n + 1)) * 1 :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

theorem summable_sixVertexOffsetConvolutionTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexOffsetConvolutionTerm lam n alpha) := by
  have hq0 : 0 <= Real.exp (-2 * lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmajor : Summable (fun n : Nat =>
      2 * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left 2
  exact hmajor.of_norm_bounded
    (fun n => norm_sixVertexOffsetConvolutionTerm_le lam n alpha)

theorem intervalIntegral_shiftedCos_mul_offsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) {m : Nat} (hm : 0 < m)
    (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((m : Real) * (alpha - beta)) *
        sixVertexOffsetRapidityProfile lam beta) =
      Real.sin ((m : Real) * alpha) *
        ((-1 : Real) ^ m * Real.tanh ((m : Real) * lam) / (m : Real)) := by
  let tau := sixVertexOffsetRapidityProfile lam
  have htau : Continuous tau :=
    continuous_sixVertexOffsetRapidityProfile hlam
  have hcosZero :
      (∫ beta in -Real.pi..Real.pi,
        Real.cos ((m : Real) * beta) * tau beta) = 0 := by
    apply intervalIntegral_neg_pi_pi_eq_zero_of_odd
    intro beta
    dsimp [tau]
    rw [show (m : Real) * -beta = -((m : Real) * beta) by ring,
      Real.cos_neg, odd_sixVertexOffsetRapidityProfile]
    ring
  have hsinCoeff :
      (∫ beta in -Real.pi..Real.pi,
        tau beta * Real.sin ((m : Real) * beta)) =
      (-1 : Real) ^ m * Real.tanh ((m : Real) * lam) / (m : Real) := by
    have h := sixVertexOffsetRapidityProfile_sineCoefficient hlam hm
    calc
      _ = Real.pi * ((1 / Real.pi) *
          ∫ beta in -Real.pi..Real.pi,
            tau beta * Real.sin ((m : Real) * beta)) := by
        field_simp [Real.pi_ne_zero]
      _ = Real.pi *
          ((-1 : Real) ^ m * Real.tanh ((m : Real) * lam) /
            (Real.pi * (m : Real))) := by rw [h]
      _ = _ := by
        field_simp [Real.pi_ne_zero,
          show (m : Real) ≠ 0 by exact_mod_cast hm.ne']
  have hcosInt : IntervalIntegrable
      (fun beta => Real.cos ((m : Real) * beta) * tau beta)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((by fun_prop : Continuous (fun beta : Real =>
      Real.cos ((m : Real) * beta))).mul htau).intervalIntegrable _ _
  have hsinInt : IntervalIntegrable
      (fun beta => Real.sin ((m : Real) * beta) * tau beta)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((by fun_prop : Continuous (fun beta : Real =>
      Real.sin ((m : Real) * beta))).mul htau).intervalIntegrable _ _
  have hpoint (beta : Real) :
      Real.cos ((m : Real) * (alpha - beta)) * tau beta =
        Real.cos ((m : Real) * alpha) *
            (Real.cos ((m : Real) * beta) * tau beta) +
          Real.sin ((m : Real) * alpha) *
            (Real.sin ((m : Real) * beta) * tau beta) := by
    rw [mul_sub, Real.cos_sub]
    ring
  rw [intervalIntegral.integral_congr (fun beta _ => hpoint beta),
    intervalIntegral.integral_add
    (hcosInt.const_mul _) (hsinInt.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hcosZero]
  have hsinComm :
      (∫ beta in -Real.pi..Real.pi,
        Real.sin ((m : Real) * beta) * tau beta) =
      ∫ beta in -Real.pi..Real.pi,
        tau beta * Real.sin ((m : Real) * beta) := by
    apply intervalIntegral.integral_congr
    intro beta _
    ring
  rw [hsinComm, hsinCoeff]
  ring

theorem intervalIntegral_XiFourierTerm_mul_offsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
        sixVertexOffsetRapidityProfile lam beta) =
      sixVertexOffsetConvolutionTerm lam n alpha := by
  unfold sixVertexXiFourierTerm sixVertexOffsetConvolutionTerm
  rw [show (fun beta : Real =>
      (2 * Real.exp (-((n + 1 : Real) * (2 * lam))) *
          Real.cos ((n + 1 : Real) * (alpha - beta))) *
          sixVertexOffsetRapidityProfile lam beta) =
      fun beta =>
        (2 * Real.exp (-((n + 1 : Real) * (2 * lam)))) *
          (Real.cos ((n + 1 : Real) * (alpha - beta)) *
            sixVertexOffsetRapidityProfile lam beta) by
    funext beta
    ring,
    intervalIntegral.integral_const_mul,
    show (∫ beta in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          sixVertexOffsetRapidityProfile lam beta) =
        Real.sin ((n + 1 : Real) * alpha) *
          ((-1 : Real) ^ (n + 1) *
            Real.tanh ((n + 1 : Real) * lam) / (n + 1 : Real)) by
      simpa only [Nat.cast_add, Nat.cast_one] using
        intervalIntegral_shiftedCos_mul_offsetRapidityProfile hlam
          (m := n + 1) (by omega) alpha]
  ring

private def XiFourierTermMulOffsetRapidityProfileContinuous
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) : C(Real, Real) :=
  ⟨fun beta => sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
      sixVertexOffsetRapidityProfile lam beta, by
    exact (by
      unfold sixVertexXiFourierTerm
      fun_prop : Continuous _).mul
        (continuous_sixVertexOffsetRapidityProfile hlam)⟩


theorem intervalIntegral_XiFourier_mul_offsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      sixVertexXiFourier (2 * lam) (alpha - beta) *
        sixVertexOffsetRapidityProfile lam beta) =
      ∑' n : Nat, sixVertexOffsetConvolutionTerm lam n alpha := by
  have h2lam : 0 < 2 * lam := by linarith
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  let tauMap : C(Real, Real) :=
    ⟨sixVertexOffsetRapidityProfile lam,
      continuous_sixVertexOffsetRapidityProfile hlam⟩
  let B : Real := ‖tauMap.restrict K‖
  have hB : 0 <= B := norm_nonneg _
  have hmajor : Summable (fun n : Nat =>
      sixVertexFourierRootDensityMajorant (2 * lam) n * B) :=
    (summable_sixVertexFourierRootDensityMajorant h2lam).mul_right B
  have hnorm : Summable (fun n : Nat =>
      ‖(XiFourierTermMulOffsetRapidityProfileContinuous
        hlam n alpha).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmajor
    rw [ContinuousMap.norm_le _ (mul_nonneg
      (by unfold sixVertexFourierRootDensityMajorant; positivity) hB)]
    intro beta
    change |sixVertexXiFourierTerm (2 * lam) n (alpha - (beta : Real)) *
        sixVertexOffsetRapidityProfile lam beta| <= _
    rw [abs_mul]
    apply mul_le_mul
    · simpa only [Real.norm_eq_abs] using
        norm_sixVertexXiFourierTerm_le (2 * lam) n (alpha - (beta : Real))
    · simpa only [Real.norm_eq_abs] using
        (tauMap.restrict K).norm_coe_le_norm beta
    · exact abs_nonneg _
    · unfold sixVertexFourierRootDensityMajorant
      positivity
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hswap' :
      (∑' n : Nat, ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta) =
      ∫ beta in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta) := by
    simpa only [XiFourierTermMulOffsetRapidityProfileContinuous] using hswap
  have htauZero :
      (∫ beta in -Real.pi..Real.pi,
        sixVertexOffsetRapidityProfile lam beta) = 0 :=
    intervalIntegral_neg_pi_pi_eq_zero_of_odd
      (odd_sixVertexOffsetRapidityProfile lam)
  have htauInt : IntervalIntegrable
      (sixVertexOffsetRapidityProfile lam) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    (continuous_sixVertexOffsetRapidityProfile hlam).intervalIntegrable _ _
  have hseriesContinuous : Continuous (fun beta =>
      (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
        sixVertexOffsetRapidityProfile lam beta) := by
    apply Continuous.mul
    · apply continuous_tsum
      · intro n
        unfold sixVertexXiFourierTerm
        fun_prop
      · exact summable_sixVertexFourierRootDensityMajorant h2lam
      · intro n beta
        exact norm_sixVertexXiFourierTerm_le (2 * lam) n (alpha - beta)
    · exact continuous_sixVertexOffsetRapidityProfile hlam
  unfold sixVertexXiFourier
  rw [show (fun beta =>
      (1 + ∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
        sixVertexOffsetRapidityProfile lam beta) =
      fun beta => sixVertexOffsetRapidityProfile lam beta +
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
          sixVertexOffsetRapidityProfile lam beta by
    funext beta
    ring]
  rw [intervalIntegral.integral_add htauInt
      (hseriesContinuous.intervalIntegrable _ _), htauZero, zero_add]
  calc
    _ = ∫ beta in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta) := by
      apply intervalIntegral.integral_congr
      intro beta _
      exact tsum_mul_right.symm
    _ = ∑' n : Nat, ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta := hswap'.symm
    _ = _ := by
      apply tsum_congr
      intro n
      exact intervalIntegral_XiFourierTerm_mul_offsetRapidityProfile
        hlam n alpha

theorem exp_neg_two_mul_one_add_tanh_eq_one_sub_tanh (x : Real) :
    Real.exp (-2 * x) * (1 + Real.tanh x) = 1 - Real.tanh x := by
  rw [Real.tanh_eq]
  have hexp : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hden : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
  have hrel : Real.exp (-2 * x) * Real.exp x = Real.exp (-x) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  field_simp [hexp, hden]
  calc
    Real.exp (-(2 * x)) *
        (Real.exp x + Real.exp (-x) + (Real.exp x - Real.exp (-x))) =
      2 * (Real.exp (-2 * x) * Real.exp x) := by ring
    _ = 2 * Real.exp (-x) := by rw [hrel]
    _ = Real.exp x + Real.exp (-x) -
        (Real.exp x - Real.exp (-x)) := by ring

theorem sixVertexOffsetSourceCorrectionTerm_sub_convolutionTerm
    (lam : Real) (n : Nat) (alpha : Real) :
    sixVertexOffsetSourceCorrectionTerm lam n alpha -
        sixVertexOffsetConvolutionTerm lam n alpha =
      2 * Real.pi * sixVertexOffsetCorrectionTerm lam n alpha := by
  let m : Real := n + 1
  let x : Real := m * lam
  have hm : m ≠ 0 := by dsimp [m]; positivity
  have hidentity := exp_neg_two_mul_one_add_tanh_eq_one_sub_tanh x
  unfold sixVertexOffsetSourceCorrectionTerm
    sixVertexOffsetConvolutionTerm sixVertexOffsetCorrectionTerm
    sixVertexGapCorrectionTerm
  dsimp [m, x] at hidentity ⊢
  have hexp : Real.exp (-2 * ((n + 1 : Real) * lam)) *
      (1 + Real.tanh ((n + 1 : Real) * lam)) =
      1 - Real.tanh ((n + 1 : Real) * lam) := hidentity
  field_simp [Real.pi_ne_zero, hm]
  calc
    Real.exp (-(2 * (n + 1 : Real) * lam)) *
        Real.sin ((n + 1 : Real) * alpha) *
          (-1 - Real.tanh ((n + 1 : Real) * lam)) =
      -(Real.exp (-2 * ((n + 1 : Real) * lam)) *
          (1 + Real.tanh ((n + 1 : Real) * lam))) *
        Real.sin ((n + 1 : Real) * alpha) := by ring
    _ = -(1 - Real.tanh ((n + 1 : Real) * lam)) *
        Real.sin ((n + 1 : Real) * alpha) := by rw [hexp]
    _ = Real.sin ((n + 1 : Real) * alpha) *
        (Real.tanh ((n + 1 : Real) * lam) - 1) := by ring



theorem sixVertexOffsetRapidityProfile_integralEquation
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    2 * Real.pi * sixVertexOffsetRapidityProfile lam alpha =
      sixVertexOffsetSourceRapidityProfile lam alpha -
        ∫ beta in -Real.pi..Real.pi,
          sixVertexXiFourier (2 * lam) (alpha - beta) *
            sixVertexOffsetRapidityProfile lam beta := by
  rw [intervalIntegral_XiFourier_mul_offsetRapidityProfile hlam alpha]
  have hsource := summable_sixVertexOffsetSourceCorrectionTerm hlam alpha
  have hconv := summable_sixVertexOffsetConvolutionTerm hlam alpha
  have hdiff := hsource.tsum_sub hconv
  unfold sixVertexOffsetRapidityProfile sixVertexOffsetSourceRapidityProfile
  rw [show -alpha +
        (∑' n : Nat, sixVertexOffsetSourceCorrectionTerm lam n alpha) -
          ∑' n : Nat, sixVertexOffsetConvolutionTerm lam n alpha =
      -alpha + ((∑' n : Nat,
        sixVertexOffsetSourceCorrectionTerm lam n alpha) -
          ∑' n : Nat, sixVertexOffsetConvolutionTerm lam n alpha) by ring,
    <- hdiff]
  have hterm :
      (∑' n : Nat, (sixVertexOffsetSourceCorrectionTerm lam n alpha -
        sixVertexOffsetConvolutionTerm lam n alpha)) =
      ∑' n : Nat, 2 * Real.pi *
        sixVertexOffsetCorrectionTerm lam n alpha := by
    apply tsum_congr
    intro n
    exact sixVertexOffsetSourceCorrectionTerm_sub_convolutionTerm lam n alpha
  rw [hterm, tsum_mul_left]
  field_simp [Real.pi_ne_zero]



theorem intervalIntegral_continuousOffsetKernel_mul_fourier_pullback
    {c : Real} (hc : 2 < c) (alpha : Real) :
    (∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c
          (sixVertexRapidityMomentum
            (sixVertexAntiferroelectricLambda c) alpha) y *
        sixVertexContinuousOffsetFourier c hc y) =
      ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c)
            (alpha - beta) *
          sixVertexOffsetRapidityProfile
            (sixVertexAntiferroelectricLambda c) beta := by
  let lam := sixVertexAntiferroelectricLambda c
  let k := sixVertexRapidityMomentum lam
  let x := k alpha
  let g : Real -> Real := fun y =>
    sixVertexContinuousOffsetKernel c x y *
      sixVertexContinuousOffsetFourier c hc y
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hweight : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have hkernel : Continuous (sixVertexContinuousOffsetKernel c x) := by
    unfold sixVertexContinuousOffsetKernel
    exact (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous.div
      hweight (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
  have hg : Continuous g :=
    hkernel.mul (continuous_sixVertexContinuousOffsetFourier hc)
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := -Real.pi) (b := Real.pi) (f := k)
    (f' := sixVertexXiFourier lam) (g := g)
    (fun beta _ => hasDerivAt_sixVertexRapidityMomentum hlam beta)
    (continuous_sixVertexXiFourier hlam).continuousOn hg
  have hkneg : k (-Real.pi) = -Real.pi :=
    sixVertexRapidityMomentum_neg_pi hlam
  have hkpi : k Real.pi = Real.pi :=
    sixVertexRapidityMomentum_pi hlam
  rw [hkneg, hkpi] at hsubst
  have hpulled :
      (∫ beta in -Real.pi..Real.pi,
        (g ∘ k) beta * sixVertexXiFourier lam beta) =
      ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourier (2 * lam) (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta := by
    apply intervalIntegral.integral_congr
    intro beta hbeta
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] :
      -Real.pi <= Real.pi)] at hbeta
    dsimp only [Function.comp_apply, g, x, k]
    unfold sixVertexContinuousOffsetKernel
    rw [sixVertexRootDensityKernel_rapidityMomentum hc,
      sixVertexRootDensityWeight_rapidityMomentum hc,
      sixVertexContinuousOffsetFourier_rapidityMomentum hc hbeta]
    have hXi : sixVertexXiFourier lam beta ≠ 0 :=
      (sixVertexXiFourier_pos hlam beta).ne'
    dsimp [lam] at hXi ⊢
    field_simp [hXi]
  change (∫ y in -Real.pi..Real.pi, g y) = _
  rw [<- hsubst, hpulled]



theorem sixVertexContinuousOffsetFourier_satisfiesEquation
    {c : Real} (hc : 2 < c) :
    SixVertexSatisfiesContinuousOffsetEquation c
      (sixVertexContinuousOffsetFourier c hc) := by
  intro x hx
  let lam := sixVertexAntiferroelectricLambda c
  let alpha := sixVertexMomentumRapidity lam
    (sixVertexAntiferroelectricLambda_pos hc) x
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hxalpha : sixVertexRapidityMomentum lam alpha = x := by
    exact sixVertexRapidityMomentum_momentumRapidity hlam hx
  have halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [alpha, sixVertexMomentumRapidity]
    exact ((sixVertexRapidityMomentumOrderIso lam hlam).symm
      (Set.projIcc (-Real.pi) Real.pi
        (by linarith [Real.pi_pos]) x)).property
  have heq := sixVertexOffsetRapidityProfile_integralEquation hlam alpha
  have htau : sixVertexContinuousOffsetFourier c hc x =
      sixVertexOffsetRapidityProfile lam alpha := by
    rw [<- hxalpha]
    exact sixVertexContinuousOffsetFourier_rapidityMomentum hc halpha
  have hsource : sixVertexContinuousOffsetSource c x =
      sixVertexOffsetSourceRapidityProfile lam alpha := by
    rw [<- hxalpha]
    exact sixVertexContinuousOffsetSource_rapidityMomentum hc alpha
  have hintegral :
      (∫ y in -Real.pi..Real.pi,
        sixVertexContinuousOffsetKernel c x y *
          sixVertexContinuousOffsetFourier c hc y) =
      ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourier (2 * lam) (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta := by
    rw [<- hxalpha]
    exact intervalIntegral_continuousOffsetKernel_mul_fourier_pullback
      hc alpha
  rw [htau, hsource, hintegral]
  exact heq

end

end StatMech.FrontierD
