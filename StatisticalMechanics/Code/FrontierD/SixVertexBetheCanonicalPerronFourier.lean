/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronLimit
import Code.FrontierD.SixVertexBetheFourierConvolution
import Code.FrontierD.SixVertexBetheFourierEvaluation
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds









open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexLogCosineSeries (r alpha : Real) : Real :=
  ∑' n : Nat,
    r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) / (n + 1 : Real)

theorem hasSum_sixVertexLogCosineSeries
    {r : Real} (hr : |r| < 1) (alpha : Real) :
    HasSum (fun n : Nat =>
      r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
        (n + 1 : Real))
      (-Real.log ‖(1 : Complex) -
        (r : Complex) * Complex.exp (Complex.I * alpha)‖) := by
  let z : Complex := (r : Complex) * Complex.exp (Complex.I * alpha)
  have hzNorm : ‖z‖ = |r| := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    simp
  have hz : ‖z‖ < 1 := by simpa [hzNorm] using hr
  have hcomplex := Complex.hasSum_taylorSeries_neg_log hz
  have hreal := Complex.hasSum_re hcomplex
  have hshift : HasSum (fun n : Nat =>
      ((z ^ (n + 1) / ((n + 1 : Nat) : Complex)).re))
      (-Complex.log (1 - z)).re := by
    simpa using
      ((hasSum_nat_add_iff'
        (f := fun n : Nat => (z ^ n / (n : Complex)).re) 1).mpr hreal)
  convert hshift using 1
  · funext n
    have hexp :
        (Complex.exp (Complex.I * alpha) ^ (n + 1)).re =
          Real.cos ((n + 1 : Real) * alpha) := by
      rw [← Complex.exp_nat_mul]
      convert Complex.exp_ofReal_mul_I_re ((n + 1 : Real) * alpha) using 2
      push_cast
      ring
    dsimp [z]
    rw [mul_pow, Complex.div_natCast_re, Complex.mul_re, hexp]
    have hre : ((r : Complex) ^ (n + 1)).re = r ^ (n + 1) := by
      rw [← Complex.ofReal_pow]
      rfl
    have him : ((r : Complex) ^ (n + 1)).im = 0 := by
      rw [← Complex.ofReal_pow]
      rfl
    rw [hre, him]
    norm_num [Nat.cast_add, Nat.cast_one]
  · simpa [z, Complex.log_re]

theorem sixVertexLogCosineSeries_eq_neg_log_norm
    {r : Real} (hr : |r| < 1) (alpha : Real) :
    sixVertexLogCosineSeries r alpha =
      -Real.log ‖(1 : Complex) -
        (r : Complex) * Complex.exp (Complex.I * alpha)‖ :=
  (hasSum_sixVertexLogCosineSeries hr alpha).tsum_eq

def sixVertexRegularizedRapidityB (lam epsilon : Real) : Real :=
  2 * (Real.cosh lam + 1) + epsilon

def sixVertexRegularizedRapidityDelta (lam epsilon : Real) : Real :=
  (2 * (Real.cosh lam + 1) + epsilon * Real.cosh lam) /
    sixVertexRegularizedRapidityB lam epsilon

def sixVertexRegularizedRapidityRadius (lam epsilon : Real) : Real :=
  Real.exp (-Real.arcosh
    (sixVertexRegularizedRapidityDelta lam epsilon))

theorem one_lt_sixVertexRegularizedRapidityDelta
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    1 < sixVertexRegularizedRapidityDelta lam epsilon := by
  have hd : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
  have hB : 0 < sixVertexRegularizedRapidityB lam epsilon := by
    unfold sixVertexRegularizedRapidityB
    positivity
  unfold sixVertexRegularizedRapidityDelta
  rw [one_lt_div hB]
  unfold sixVertexRegularizedRapidityB
  nlinarith

theorem sixVertexRegularizedRapidityRadius_mem_Ioo
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    sixVertexRegularizedRapidityRadius lam epsilon ∈ Set.Ioo 0 1 := by
  let delta := sixVertexRegularizedRapidityDelta lam epsilon
  have hdelta : 1 < delta :=
    one_lt_sixVertexRegularizedRapidityDelta hlam hepsilon
  have hmu : 0 < Real.arcosh delta := Real.arcosh_pos hdelta
  constructor
  · unfold sixVertexRegularizedRapidityRadius
    positivity
  · unfold sixVertexRegularizedRapidityRadius
    rw [Real.exp_lt_one_iff]
    linarith

theorem sixVertexRegularizedRapidityDelta_eq_radius
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    sixVertexRegularizedRapidityDelta lam epsilon =
      (sixVertexRegularizedRapidityRadius lam epsilon +
        (sixVertexRegularizedRapidityRadius lam epsilon)⁻¹) / 2 := by
  let delta := sixVertexRegularizedRapidityDelta lam epsilon
  let mu := Real.arcosh delta
  let r := Real.exp (-mu)
  have hdelta : 1 ≤ delta :=
    (one_lt_sixVertexRegularizedRapidityDelta hlam hepsilon).le
  have hcosh : Real.cosh mu = delta := Real.cosh_arcosh hdelta
  change delta = (r + r⁻¹) / 2
  rw [← hcosh, Real.cosh_eq]
  dsimp [r]
  rw [Real.exp_neg, inv_inv]
  ring

private theorem neg_pi_le_pi : -Real.pi ≤ Real.pi := by
  linarith [Real.pi_pos]



theorem intervalIntegral_mul_sixVertexFourierPhysicalDensity_eq_rapidity
    {c : Real} (hc : 2 < c) {f : Real → Real} (hf : Continuous f) :
    (∫ x in -Real.pi..Real.pi,
      f x * sixVertexFourierPhysicalDensity c hc x) =
      (1 / (2 * Real.pi)) *
        ∫ alpha in -Real.pi..Real.pi,
          f (sixVertexRapidityMomentum
              (sixVertexAntiferroelectricLambda c) alpha) *
            sixVertexFourierRootDensity
              (sixVertexAntiferroelectricLambda c) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  let g : Real → Real := fun x =>
    f x * sixVertexFourierPhysicalDensity c hc x
  have hg : Continuous g :=
    hf.mul (continuous_sixVertexFourierPhysicalDensity hc)
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := -Real.pi) (b := Real.pi)
    (f := sixVertexRapidityMomentum lam)
    (f' := sixVertexXiFourier lam) (g := g)
    (fun alpha _ => hasDerivAt_sixVertexRapidityMomentum hlam alpha)
    (continuous_sixVertexXiFourier hlam).continuousOn hg
  rw [sixVertexRapidityMomentum_neg_pi hlam,
    sixVertexRapidityMomentum_pi hlam] at hsubst
  rw [← hsubst]
  have hpull :
      (∫ alpha in -Real.pi..Real.pi,
        (g ∘ sixVertexRapidityMomentum lam) alpha *
          sixVertexXiFourier lam alpha) =
      ∫ alpha in -Real.pi..Real.pi,
        (f (sixVertexRapidityMomentum lam alpha) *
          sixVertexFourierRootDensity lam alpha) / (2 * Real.pi) := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    rw [Set.uIcc_of_le neg_pi_le_pi] at halpha
    dsimp only [Function.comp_apply, g]
    rw [sixVertexFourierPhysicalDensity_rapidityMomentum hc halpha]
    have hXi : sixVertexXiFourier lam alpha ≠ 0 :=
      (sixVertexXiFourier_pos hlam alpha).ne'
    dsimp [lam] at hXi ⊢
    field_simp [hXi, Real.pi_ne_zero]
  rw [hpull]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  ring

theorem sixVertexBetheLogNumerator_rapidityMomentum
    {c : Real} (hc : 2 < c) (alpha : Real) :
    sixVertexBetheLogNumerator c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) =
      2 * (Real.cosh (sixVertexAntiferroelectricLambda c) + 1) *
        (Real.cosh (2 * sixVertexAntiferroelectricLambda c) -
          Real.cos alpha) /
        (Real.cosh (sixVertexAntiferroelectricLambda c) -
          Real.cos alpha) := by
  let lam := sixVertexAntiferroelectricLambda c
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hd : Real.cosh lam - Real.cos alpha ≠ 0 := by
    have := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  have hrel := sixVertex_cosh_antiferroelectricLambda hc
  have hhyper := Real.cosh_sq_sub_sinh_sq lam
  rw [sixVertexBetheLogNumerator,
    cos_sixVertexRapidityMomentum hlam]
  rw [Real.cosh_two_mul]
  rw [eq_div_iff hd]
  field_simp [hd]
  dsimp [lam] at hrel hhyper ⊢
  rw [hrel] at hhyper ⊢
  ring_nf at hhyper ⊢
  nlinarith

theorem sixVertexBetheLogDenominator_rapidityMomentum
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    sixVertexBetheLogDenominator
          (sixVertexRapidityMomentum
            (sixVertexAntiferroelectricLambda c) alpha) + epsilon =
      sixVertexRegularizedRapidityB
          (sixVertexAntiferroelectricLambda c) epsilon *
        (sixVertexRegularizedRapidityDelta
            (sixVertexAntiferroelectricLambda c) epsilon -
          Real.cos alpha) /
        (Real.cosh (sixVertexAntiferroelectricLambda c) -
          Real.cos alpha) := by
  let lam := sixVertexAntiferroelectricLambda c
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hd : Real.cosh lam - Real.cos alpha ≠ 0 := by
    have := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  rw [sixVertexBetheLogDenominator,
    cos_sixVertexRapidityMomentum hlam]
  unfold sixVertexRegularizedRapidityDelta
  have hB : sixVertexRegularizedRapidityB lam epsilon ≠ 0 := by
    unfold sixVertexRegularizedRapidityB
    positivity
  unfold sixVertexRegularizedRapidityB
  dsimp [lam] at hd hB ⊢
  field_simp [hd, hB]
  ring

private def sixVertexRapidityCompact : TopologicalSpace.Compacts Real :=
  ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩

private def sixVertexAbelLogTermMulRootDensityContinuous
    {lam : Real} (hlam : 0 < lam) (r : Real) (n : Nat) : C(Real, Real) :=
  ⟨fun alpha =>
      (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
        (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha,
    (by
      apply Continuous.mul
      · fun_prop
      · exact continuous_sixVertexFourierRootDensity hlam)⟩

private theorem summable_sixVertexAbelLogTermMulRootDensityNorm
    {lam r : Real} (hlam : 0 < lam) (hr : |r| < 1) :
    Summable (fun n : Nat =>
      ‖(sixVertexAbelLogTermMulRootDensityContinuous hlam r n).restrict
        sixVertexRapidityCompact‖) := by
  have hgeom : Summable (fun n : Nat => |r| ^ (n + 1)) :=
    (summable_geometric_of_lt_one (abs_nonneg r) hr).comp_injective
      Nat.succ_injective
  apply (hgeom.mul_right
    (sixVertexFourierRootDensityNormBound lam)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [ContinuousMap.norm_le _
    (mul_nonneg (pow_nonneg (abs_nonneg r) _)
      (sixVertexFourierRootDensityNormBound_nonneg lam))]
  intro alpha
  change ‖(r ^ (n + 1) * Real.cos ((n + 1 : Real) * (alpha : Real)) /
      (n + 1 : Real) * sixVertexFourierRootDensity lam alpha)‖ <= _
  rw [norm_mul]
  apply mul_le_mul
  · rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
    have hcos : |Real.cos ((n + 1 : Real) * (alpha : Real))| <= 1 :=
      abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hden : 1 <= |(n + 1 : Real)| := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    calc
      |r| ^ (n + 1) * |Real.cos ((n + 1 : Real) * (alpha : Real))| /
          |(n + 1 : Real)| <= |r| ^ (n + 1) * 1 / 1 := by
            gcongr
      _ = |r| ^ (n + 1) := by ring
  · exact norm_sixVertexFourierRootDensity_le hlam alpha
  · exact norm_nonneg _
  · exact pow_nonneg (abs_nonneg r) _




theorem intervalIntegral_sixVertexLogCosineSeries_mul_rootDensity
    {lam r : Real} (hlam : 0 < lam) (hr : |r| < 1) :
    (∫ alpha in -Real.pi..Real.pi,
      sixVertexLogCosineSeries r alpha *
        sixVertexFourierRootDensity lam alpha) =
      ∑' n : Nat, Real.pi * r ^ (n + 1) /
        ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam)) := by
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (summable_sixVertexAbelLogTermMulRootDensityNorm hlam hr)
  have hswap' :
      (∑' n : Nat, ∫ alpha in -Real.pi..Real.pi,
        (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
          (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha) =
      ∫ alpha in -Real.pi..Real.pi,
        ∑' n : Nat,
          (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
            (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha := by
    simpa only [sixVertexAbelLogTermMulRootDensityContinuous] using hswap
  rw [show (∫ alpha in -Real.pi..Real.pi,
      sixVertexLogCosineSeries r alpha *
        sixVertexFourierRootDensity lam alpha) =
      ∫ alpha in -Real.pi..Real.pi,
        ∑' n : Nat,
          (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
            (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha by
    apply intervalIntegral.integral_congr
    intro alpha _
    unfold sixVertexLogCosineSeries
    exact tsum_mul_right.symm]
  rw [← hswap']
  apply tsum_congr
  intro n
  have hcos := intervalIntegral_shiftedCos_mul_sixVertexFourierRootDensity
    hlam n 0
  have hcos' :
      (∫ alpha in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * alpha) *
          sixVertexFourierRootDensity lam alpha) =
        Real.pi / Real.cosh ((n + 1 : Real) * lam) := by
    convert hcos using 1 <;> simp [Real.cos_neg]
  simp_rw [show ∀ alpha : Real,
      (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
          (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha =
        (r ^ (n + 1) / (n + 1 : Real)) *
          (Real.cos ((n + 1 : Real) * alpha) *
            sixVertexFourierRootDensity lam alpha) by
      intro alpha
      ring]
  rw [intervalIntegral.integral_const_mul, hcos']
  field_simp [(Real.cosh_pos ((n + 1 : Real) * lam)).ne']


def sixVertexFreeEnergyRapidityRadius (lam : Real) : Real :=
  Real.exp (-2 * lam)

theorem sixVertexFreeEnergyRapidityRadius_mem_Ioo
    {lam : Real} (hlam : 0 < lam) :
    sixVertexFreeEnergyRapidityRadius lam ∈ Set.Ioo 0 1 := by
  constructor
  · unfold sixVertexFreeEnergyRapidityRadius
    positivity
  · unfold sixVertexFreeEnergyRapidityRadius
    rw [Real.exp_lt_one_iff]
    linarith

theorem cosh_two_eq_sixVertexFreeEnergyRapidityRadius
    (lam : Real) :
    Real.cosh (2 * lam) =
      (sixVertexFreeEnergyRapidityRadius lam +
        (sixVertexFreeEnergyRapidityRadius lam)⁻¹) / 2 := by
  unfold sixVertexFreeEnergyRapidityRadius
  have hinv : (Real.exp (-2 * lam))⁻¹ = Real.exp (2 * lam) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [Real.cosh_eq, show -(2 * lam) = -2 * lam by ring, hinv,
    add_comm]

theorem sq_norm_one_sub_radius_exp_mul_I
    (r alpha : Real) :
    ‖(1 : Complex) -
        (r : Complex) * Complex.exp (Complex.I * alpha)‖ ^ 2 =
      1 - 2 * r * Real.cos alpha + r ^ 2 := by
  rw [show Complex.I * (alpha : Complex) =
      (alpha : Complex) * Complex.I by ring]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.mul_re, Complex.mul_im]
  nlinarith [Real.sin_sq_add_cos_sq alpha]



theorem log_radius_add_inv_div_two_sub_cos
    {r : Real} (hr : r ∈ Set.Ioo 0 1) (alpha : Real) :
    Real.log ((r + r⁻¹) / 2 - Real.cos alpha) =
      2 * Real.log ‖(1 : Complex) -
          (r : Complex) * Complex.exp (Complex.I * alpha)‖ -
        Real.log (2 * r) := by
  have hr0 : 0 < r := hr.1
  have honeSub : 1 - r ≠ 0 := by linarith [hr.2]
  have hsquare : 0 < (1 - r) ^ 2 := sq_pos_of_ne_zero honeSub
  have hdelta : 1 < (r + r⁻¹) / 2 := by
    rw [one_lt_div (by norm_num : (0 : Real) < 2)]
    have hrepr : r + r⁻¹ - 2 = (1 - r) ^ 2 / r := by
      field_simp [hr0.ne']
      ring
    have : 0 < r + r⁻¹ - 2 := by
      rw [hrepr]
      exact div_pos hsquare hr0
    linarith
  have harg :
      (r + r⁻¹) / 2 - Real.cos alpha =
        ‖(1 : Complex) -
          (r : Complex) * Complex.exp (Complex.I * alpha)‖ ^ 2 /
            (2 * r) := by
    rw [sq_norm_one_sub_radius_exp_mul_I]
    field_simp [hr0.ne']
    ring
  have hleft : 0 < (r + r⁻¹) / 2 - Real.cos alpha := by
    linarith [Real.cos_le_one alpha]
  have hnorm :
      ‖(1 : Complex) -
        (r : Complex) * Complex.exp (Complex.I * alpha)‖ ≠ 0 := by
    intro hzero
    have hsqzero :
        ‖(1 : Complex) -
          (r : Complex) * Complex.exp (Complex.I * alpha)‖ ^ 2 = 0 := by
      rw [hzero]
      norm_num
    rw [hsqzero, zero_div] at harg
    linarith
  rw [harg, Real.log_div (pow_ne_zero 2 hnorm)
    (mul_ne_zero (by norm_num) hr0.ne'), Real.log_pow]
  norm_num


def sixVertexRegularizedRapidityConstant (lam epsilon : Real) : Real :=
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  (1 / 2 : Real) *
    (Real.log (2 * (Real.cosh lam + 1)) -
      Real.log (sixVertexRegularizedRapidityB lam epsilon) -
      Real.log (2 * q) + Real.log (2 * r))

theorem sixVertexRegularizedBetheLogKernel_rapidityMomentum_eq_series
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) =
      sixVertexRegularizedRapidityConstant
          (sixVertexAntiferroelectricLambda c) epsilon +
        sixVertexLogCosineSeries
          (sixVertexRegularizedRapidityRadius
            (sixVertexAntiferroelectricLambda c) epsilon) alpha -
        sixVertexLogCosineSeries
          (sixVertexFreeEnergyRapidityRadius
            (sixVertexAntiferroelectricLambda c)) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hq : q ∈ Set.Ioo 0 1 :=
    sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr : r ∈ Set.Ioo 0 1 :=
    sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  have hqAbs : |q| < 1 := by
    rw [abs_of_pos hq.1]
    exact hq.2
  have hrAbs : |r| < 1 := by
    rw [abs_of_pos hr.1]
    exact hr.2
  have hd : 0 < Real.cosh lam - Real.cos alpha := by
    have := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  have hD : 0 < Real.cosh (2 * lam) - Real.cos alpha := by
    have h2lam : 0 < 2 * lam := by positivity
    have := Real.one_lt_cosh.mpr h2lam.ne'
    linarith [Real.cos_le_one alpha]
  have hdelta : 0 < sixVertexRegularizedRapidityDelta lam epsilon -
      Real.cos alpha := by
    have := one_lt_sixVertexRegularizedRapidityDelta hlam hepsilon
    linarith [Real.cos_le_one alpha]
  have hA : 0 < 2 * (Real.cosh lam + 1) := by positivity
  have hB : 0 < sixVertexRegularizedRapidityB lam epsilon := by
    unfold sixVertexRegularizedRapidityB
    positivity
  have hnum := sixVertexBetheLogNumerator_rapidityMomentum hc alpha
  have hden := sixVertexBetheLogDenominator_rapidityMomentum
    hc hepsilon alpha
  have hqlog :
      Real.log (Real.cosh (2 * lam) - Real.cos alpha) =
        2 * Real.log ‖(1 : Complex) -
            (q : Complex) * Complex.exp (Complex.I * alpha)‖ -
          Real.log (2 * q) := by
    rw [cosh_two_eq_sixVertexFreeEnergyRapidityRadius]
    exact log_radius_add_inv_div_two_sub_cos hq alpha
  have hrlog :
      Real.log (sixVertexRegularizedRapidityDelta lam epsilon -
          Real.cos alpha) =
        2 * Real.log ‖(1 : Complex) -
            (r : Complex) * Complex.exp (Complex.I * alpha)‖ -
          Real.log (2 * r) := by
    rw [sixVertexRegularizedRapidityDelta_eq_radius hlam hepsilon]
    exact log_radius_add_inv_div_two_sub_cos hr alpha
  have hnumlog :
      Real.log (sixVertexBetheLogNumerator c
          (sixVertexRapidityMomentum lam alpha)) =
        Real.log (2 * (Real.cosh lam + 1)) +
          Real.log (Real.cosh (2 * lam) - Real.cos alpha) -
          Real.log (Real.cosh lam - Real.cos alpha) := by
    rw [hnum]
    rw [Real.log_div (mul_ne_zero hA.ne' hD.ne') hd.ne',
      Real.log_mul hA.ne' hD.ne']
  have hdenlog :
      Real.log (sixVertexBetheLogDenominator
          (sixVertexRapidityMomentum lam alpha) + epsilon) =
        Real.log (sixVertexRegularizedRapidityB lam epsilon) +
          Real.log (sixVertexRegularizedRapidityDelta lam epsilon -
            Real.cos alpha) -
          Real.log (Real.cosh lam - Real.cos alpha) := by
    rw [hden]
    rw [Real.log_div (mul_ne_zero hB.ne' hdelta.ne') hd.ne',
      Real.log_mul hB.ne' hdelta.ne']
  rw [sixVertexRegularizedBetheLogKernel, hnumlog, hdenlog,
    hqlog, hrlog,
    sixVertexLogCosineSeries_eq_neg_log_norm
      (by simpa only [r] using hrAbs),
    sixVertexLogCosineSeries_eq_neg_log_norm
      (by simpa only [q] using hqAbs)]
  dsimp [sixVertexRegularizedRapidityConstant, lam, q, r]
  ring

def sixVertexAbelRootDensitySeriesTerm
    (lam r : Real) (n : Nat) : Real :=
  r ^ (n + 1) /
    ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam))

theorem summable_sixVertexAbelRootDensitySeriesTerm
    {lam r : Real} (hr : |r| < 1) :
    Summable (sixVertexAbelRootDensitySeriesTerm lam r) := by
  have hgeom : Summable (fun n : Nat => |r| ^ (n + 1)) :=
    (summable_geometric_of_lt_one (abs_nonneg r) hr).comp_injective
      Nat.succ_injective
  apply hgeom.of_norm_bounded
  intro n
  rw [sixVertexAbelRootDensitySeriesTerm, Real.norm_eq_abs, abs_div,
    abs_pow, abs_of_pos (mul_pos (by positivity) (Real.cosh_pos _))]
  have hm : 1 <= (n + 1 : Real) := by norm_num
  have hcosh : 1 <= Real.cosh ((n + 1 : Real) * lam) := by
    exact Real.one_le_cosh _
  have hden : 1 <=
      (n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam) := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ <= (n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam) :=
        mul_le_mul hm hcosh zero_le_one (by linarith [hm])
  rw [div_le_iff₀ (mul_pos (by positivity) (Real.cosh_pos _))]
  exact le_mul_of_one_le_right (pow_nonneg (abs_nonneg r) _) hden


def sixVertexRegularizedRapidityFourierValue
    (lam epsilon : Real) : Real :=
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  sixVertexRegularizedRapidityConstant lam epsilon / 2 +
    (1 / 2 : Real) *
      ∑' n : Nat,
        (sixVertexAbelRootDensitySeriesTerm lam r n -
          sixVertexAbelRootDensitySeriesTerm lam q n)



theorem sixVertexCanonicalPerronRegularizedIntegral_eq_fourierValue
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    (∫ y in -Real.pi..Real.pi,
      sixVertexRegularizedBetheLogKernel c epsilon y *
        sixVertexFourierPhysicalDensity c hc y) =
      sixVertexRegularizedRapidityFourierValue
        (sixVertexAntiferroelectricLambda c) epsilon := by
  let lam := sixVertexAntiferroelectricLambda c
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  let C := sixVertexRegularizedRapidityConstant lam epsilon
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hq : q ∈ Set.Ioo 0 1 :=
    sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr : r ∈ Set.Ioo 0 1 :=
    sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  have hqAbs : |q| < 1 := by rw [abs_of_pos hq.1]; exact hq.2
  have hrAbs : |r| < 1 := by rw [abs_of_pos hr.1]; exact hr.2
  have hSr : Continuous (sixVertexLogCosineSeries r) := by
    apply continuous_tsum
    · intro n
      fun_prop
    · exact (summable_geometric_of_lt_one (abs_nonneg r) hrAbs).comp_injective
        Nat.succ_injective
    · intro n alpha
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
      have hcos : |Real.cos ((n + 1 : Real) * alpha)| <= 1 :=
        abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have hm : 1 <= |(n + 1 : Real)| := by
        have hpos : (0 : Real) < (n : Real) + 1 := by positivity
        rw [abs_of_pos hpos]
        norm_num
      calc
        |r| ^ (n + 1) * |Real.cos ((n + 1 : Real) * alpha)| /
            |(n + 1 : Real)| <= |r| ^ (n + 1) * 1 / 1 := by gcongr
        _ = |r| ^ (n + 1) := by ring
  have hSq : Continuous (sixVertexLogCosineSeries q) := by
    apply continuous_tsum
    · intro n
      fun_prop
    · exact (summable_geometric_of_lt_one (abs_nonneg q) hqAbs).comp_injective
        Nat.succ_injective
    · intro n alpha
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
      have hcos : |Real.cos ((n + 1 : Real) * alpha)| <= 1 :=
        abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have hm : 1 <= |(n + 1 : Real)| := by
        have hpos : (0 : Real) < (n : Real) + 1 := by positivity
        rw [abs_of_pos hpos]
        norm_num
      calc
        |q| ^ (n + 1) * |Real.cos ((n + 1 : Real) * alpha)| /
            |(n + 1 : Real)| <= |q| ^ (n + 1) * 1 / 1 := by gcongr
        _ = |q| ^ (n + 1) := by ring
  rw [intervalIntegral_mul_sixVertexFourierPhysicalDensity_eq_rapidity
    hc (continuous_sixVertexRegularizedBetheLogKernel hc hepsilon)]
  have hpoint : ∀ alpha : Real,
      sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexRapidityMomentum lam alpha) *
        sixVertexFourierRootDensity lam alpha =
      ((C + sixVertexLogCosineSeries r alpha) *
          sixVertexFourierRootDensity lam alpha) -
        sixVertexLogCosineSeries q alpha *
          sixVertexFourierRootDensity lam alpha := by
    intro alpha
    rw [sixVertexRegularizedBetheLogKernel_rapidityMomentum_eq_series
      hc hepsilon]
    dsimp only [lam, q, r, C]
    ring
  rw [intervalIntegral.integral_congr (fun alpha _ => hpoint alpha)]
  have hR := continuous_sixVertexFourierRootDensity hlam
  have hCR : IntervalIntegrable
      (fun alpha => C * sixVertexFourierRootDensity lam alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((continuous_const : Continuous (fun _ : Real => C)).mul hR)
      |>.intervalIntegrable _ _
  have hSrR : IntervalIntegrable
      (fun alpha => sixVertexLogCosineSeries r alpha *
        sixVertexFourierRootDensity lam alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hSr.mul hR).intervalIntegrable _ _
  have hSqR : IntervalIntegrable
      (fun alpha => sixVertexLogCosineSeries q alpha *
        sixVertexFourierRootDensity lam alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hSq.mul hR).intervalIntegrable _ _
  have hCSrR : IntervalIntegrable
      (fun alpha => (C + sixVertexLogCosineSeries r alpha) *
        sixVertexFourierRootDensity lam alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (((continuous_const : Continuous (fun _ : Real => C)).add hSr).mul hR)
      |>.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hCSrR hSqR]
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add hCR hSrR,
    intervalIntegral.integral_const_mul,
    intervalIntegral_sixVertexFourierRootDensity hlam,
    intervalIntegral_sixVertexLogCosineSeries_mul_rootDensity hlam hrAbs,
    intervalIntegral_sixVertexLogCosineSeries_mul_rootDensity hlam hqAbs]
  have hsumr := summable_sixVertexAbelRootDensitySeriesTerm
    (lam := lam) hrAbs
  have hsumq := summable_sixVertexAbelRootDensitySeriesTerm
    (lam := lam) hqAbs
  have hpir : (∑' n : Nat,
      Real.pi * r ^ (n + 1) /
          ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam))) =
      Real.pi * ∑' n : Nat,
        sixVertexAbelRootDensitySeriesTerm lam r n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold sixVertexAbelRootDensitySeriesTerm
    ring
  have hpiq : (∑' n : Nat,
      Real.pi * q ^ (n + 1) /
          ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam))) =
      Real.pi * ∑' n : Nat,
        sixVertexAbelRootDensitySeriesTerm lam q n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold sixVertexAbelRootDensitySeriesTerm
    ring
  rw [hpir, hpiq]
  rw [show C * Real.pi + Real.pi * (∑' n : Nat,
        sixVertexAbelRootDensitySeriesTerm lam r n) -
      Real.pi * (∑' n : Nat,
        sixVertexAbelRootDensitySeriesTerm lam q n) =
      C * Real.pi + Real.pi *
        ((∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam r n) -
          ∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n) by ring,
    ← hsumr.tsum_sub hsumq]
  unfold sixVertexRegularizedRapidityFourierValue
  dsimp only [lam, q, r, C]
  field_simp [Real.pi_ne_zero]
  <;> ring

end

end StatMech.FrontierD
