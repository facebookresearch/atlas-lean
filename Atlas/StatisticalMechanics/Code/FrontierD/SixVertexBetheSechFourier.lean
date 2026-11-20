/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFourierPhysicalFamily
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim





open Filter MeasureTheory Set Topology
open scoped FourierTransform

namespace StatMech.FrontierD

noncomputable section

private theorem image_logistic_Ioo :
    (fun t : Real => t / (1 - t)) '' Set.Ioo 0 1 = Set.Ioi 0 := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact div_pos ht.1 (sub_pos.mpr ht.2)
  · intro hy
    let t := y / (1 + y)
    have hy' : 0 < y := hy
    have hden : 0 < 1 + y := by linarith
    have ht : t ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · exact div_pos hy hden
      · rw [div_lt_one hden]
        linarith
    refine ⟨t, ht, ?_⟩
    dsimp [t]
    field_simp [hden.ne']
    ring

private theorem hasDerivWithinAt_logistic
    (t : Real) (ht : t ∈ Set.Ioo 0 1) :
    HasDerivWithinAt (fun s : Real => s / (1 - s))
      (1 / (1 - t) ^ 2) (Set.Ioo 0 1) t := by
  have hne : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
  convert ((hasDerivAt_id t).div
    ((hasDerivAt_id t).const_sub 1) hne).hasDerivWithinAt using 1
  simp only [id_eq]
  field_simp [hne]
  ring

private theorem injOn_logistic :
    Set.InjOn (fun t : Real => t / (1 - t)) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  have hxden : 0 < 1 - x := sub_pos.mpr hx.2
  have hyden : 0 < 1 - y := sub_pos.mpr hy.2
  rw [div_eq_div_iff hxden.ne' hyden.ne'] at hxy
  linarith

theorem integral_Ioi_cpow_div_one_add
    (u : Complex) :
    (∫ y : Real in Set.Ioi 0,
      (y : Complex) ^ (u - 1) / (1 + y)) =
      Complex.betaIntegral u (1 - u) := by
  let f : Real → Real := fun t => t / (1 - t)
  let f' : Real → Real := fun t => 1 / (1 - t) ^ 2
  let g : Real → Complex := fun y =>
    (y : Complex) ^ (u - 1) / (1 + y)
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (0 : Real) 1) measurableSet_Ioo
    (fun t ht => hasDerivWithinAt_logistic t ht)
    injOn_logistic g
  rw [image_logistic_Ioo] at hchange
  rw [hchange]
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num)]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hft : 0 < f t := div_pos ht0 ht1
  have hf' : 0 < f' t := by
    dsimp [f']
    positivity
  dsimp [f, f', g] at hf' ⊢
  rw [abs_of_pos hf']
  rw [show t / (1 - t) = t * (1 / (1 - t)) by ring]
  rw [Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg ht0.le
    (one_div_nonneg.mpr ht1.le)]
  push_cast
  have hbase : (1 : Complex) - t = ((1 - t : Real) : Complex) := by
    norm_num
  have hbaseNe : (1 : Complex) - t ≠ 0 := by
    rw [hbase]
    exact Complex.ofReal_ne_zero.mpr ht1.ne'
  have harg : ((1 - (t : Complex))).arg ≠ Real.pi := by
    rw [hbase]
    rw [Complex.arg_ofReal_of_nonneg ht1.le]
    exact Real.pi_ne_zero.symm
  simp only [one_div]
  rw [Complex.inv_cpow (1 - t) (u - 1) harg]
  rw [← Complex.cpow_neg]
  rw [show (1 : Complex) + (t : Complex) *
        ((1 : Complex) - t)⁻¹ = ((1 : Complex) - t)⁻¹ by
    field_simp [hbaseNe]
    ring]
  rw [div_inv_eq_mul]
  rw [show (1 - u : Complex) - 1 = -u by ring]
  let B : Complex := 1 - t
  have hBne : B ≠ 0 := hbaseNe
  have hInvSq : (B ^ 2)⁻¹ = B ^ (-(2 : Complex)) := by
    calc
      (B ^ 2)⁻¹ = (B ^ (2 : Complex))⁻¹ := by
        exact congrArg Inv.inv (Complex.cpow_natCast B 2).symm
      _ = B ^ (-(2 : Complex)) := (Complex.cpow_neg B 2).symm
  have hpow : (B ^ 2)⁻¹ * (B ^ (-(u - 1)) * B) = B ^ (-u) := by
    rw [hInvSq]
    conv_lhs =>
      rhs
      rhs
      rw [show B = B ^ (1 : Complex) by rw [Complex.cpow_one]]
    rw [← Complex.cpow_add _ _ hBne, ← Complex.cpow_add _ _ hBne]
    congr 1
    ring
  have hpow' : (((1 : Complex) - t) ^ 2)⁻¹ *
      (((1 : Complex) - t) ^ (-(u - 1)) * ((1 : Complex) - t)) =
      ((1 : Complex) - t) ^ (-u) := by
    simpa only [B] using hpow
  rw [show (((1 : Complex) - t) ^ 2)⁻¹ *
      ((t : Complex) ^ (u - 1) *
        ((1 : Complex) - t) ^ (-(u - 1)) * ((1 : Complex) - t)) =
    (t : Complex) ^ (u - 1) *
      ((((1 : Complex) - t) ^ 2)⁻¹ *
        (((1 : Complex) - t) ^ (-(u - 1)) * ((1 : Complex) - t))) by
      ring,
    hpow']

private theorem image_exp_univ :
    Real.exp '' Set.univ = Set.Ioi 0 := by
  rw [Set.image_univ, Real.range_exp]

theorem integral_cexp_mul_div_one_add_rexp
    (u : Complex) :
    (∫ x : Real, Complex.exp (u * x) / (1 + Real.exp x)) =
      Complex.betaIntegral u (1 - u) := by
  let g : Real → Complex := fun y =>
    (y : Complex) ^ (u - 1) / (1 + y)
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [image_exp_univ] at hchange
  rw [← integral_Ioi_cpow_div_one_add u, hchange]
  simp only [Measure.restrict_univ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  dsimp [g]
  rw [abs_of_pos (Real.exp_pos x)]
  symm
  change (Real.exp x : Complex) *
      ((Real.exp x : Complex) ^ (u - 1) /
        (1 + (Real.exp x : Complex))) =
    Complex.exp (u * x) / (1 + (Real.exp x : Complex))
  have hexp : Complex.exp (x : Complex) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.ofReal_exp]
  conv_lhs =>
    lhs
    rw [show Complex.exp (x : Complex) =
      Complex.exp (x : Complex) ^ (1 : Complex) by
        rw [Complex.cpow_one]]
  rw [show Complex.exp (x : Complex) ^ (1 : Complex) *
      (Complex.exp (x : Complex) ^ (u - 1) /
        (1 + Complex.exp (x : Complex))) =
      (Complex.exp (x : Complex) ^ (1 : Complex) *
        Complex.exp (x : Complex) ^ (u - 1)) /
          (1 + Complex.exp (x : Complex)) by ring]
  rw [← Complex.cpow_add _ _ hexp]
  rw [Complex.cpow_def_of_ne_zero hexp]
  rw [Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  congr 1
  ring_nf

theorem betaIntegral_one_sub_eq_pi_div_sin
    {u : Complex} (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    Complex.betaIntegral u (1 - u) =
      Real.pi / Complex.sin (Real.pi * u) := by
  have hv : 0 < (1 - u).re := by
    change 0 < 1 - u.re
    linarith
  have hGamma := Complex.Gamma_mul_Gamma_eq_betaIntegral hu0 hv
  calc
    Complex.betaIntegral u (1 - u) =
        Complex.Gamma 1 * Complex.betaIntegral u (1 - u) := by
          rw [Complex.Gamma_one, one_mul]
    _ = Complex.Gamma u * Complex.Gamma (1 - u) := by
      rw [show u + (1 - u) = (1 : Complex) by ring] at hGamma
      exact hGamma.symm
    _ = Real.pi / Complex.sin (Real.pi * u) :=
      Complex.Gamma_mul_Gamma_one_sub u

theorem betaIntegral_half_sub_mul_I
    (t : Real) :
    Complex.betaIntegral
        ((1 : Complex) / 2 - (t / Real.pi) * Complex.I)
        (1 - ((1 : Complex) / 2 - (t / Real.pi) * Complex.I)) =
      Real.pi / Real.cosh t := by
  let u : Complex := (1 : Complex) / 2 - (t / Real.pi) * Complex.I
  have hu0 : 0 < u.re := by simp [u]
  have hu1 : u.re < 1 := by norm_num [u]
  rw [betaIntegral_one_sub_eq_pi_div_sin hu0 hu1]
  have harg : (Real.pi : Complex) * u =
      (Real.pi : Complex) / 2 - (t : Complex) * Complex.I := by
    dsimp [u]
    field_simp [Real.pi_ne_zero]
  rw [harg, Complex.sin_pi_div_two_sub, Complex.cos_mul_I]
  rw [← Complex.ofReal_cosh]

private theorem one_div_cosh_eq_two_mul_exp_div
    (x : Real) :
    1 / Real.cosh x =
      2 * Real.exp x / (1 + Real.exp (2 * x)) := by
  rw [Real.cosh_eq]
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero _
  have hneg : Real.exp (-x) = (Real.exp x)⁻¹ := by
    rw [← Real.exp_neg]
  have htwo : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [hneg, htwo]
  field_simp [hexp]
  ring

theorem integral_fourier_sech
    {lam : Real} (hlam : 0 < lam) (n : Real) :
    (∫ x : Real,
      Complex.exp ((-2 * Real.pi * (x * n) : Real) * Complex.I) /
        Real.cosh (Real.pi ^ 2 * x / lam)) =
      (lam / Real.pi : Real) / Real.cosh (n * lam) := by
  let A : Real := Real.pi ^ 2 / lam
  let b : Real := 2 * A
  let u : Complex :=
    (1 : Complex) / 2 - ((n * lam) / Real.pi) * Complex.I
  let g : Real → Complex := fun t =>
    Complex.exp (u * t) / (1 + Real.exp t)
  have hA : 0 < A := div_pos (sq_pos_of_pos Real.pi_pos) hlam
  have hb : 0 < b := mul_pos (by norm_num) hA
  have hpoint (x : Real) :
      Complex.exp ((-2 * Real.pi * (x * n) : Real) * Complex.I) /
          Real.cosh (Real.pi ^ 2 * x / lam) =
        2 * g (b * x) := by
    have hscale : Real.pi ^ 2 * x / lam = A * x := by
      dsimp [A]
      field_simp [hlam.ne']
    rw [hscale, div_eq_mul_inv]
    have hsechC : ((Real.cosh (A * x) : Real) : Complex)⁻¹ =
        ((2 * Real.exp (A * x) /
          (1 + Real.exp (2 * (A * x))) : Real) : Complex) := by
      rw [← Complex.ofReal_inv]
      exact congrArg (fun r : Real => (r : Complex))
        (by simpa [one_div] using
          one_div_cosh_eq_two_mul_exp_div (A * x))
    rw [hsechC]
    dsimp [g]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    push_cast
    have hden : Complex.exp (2 * ((A : Complex) * x)) =
        Complex.exp ((b : Complex) * x) := by
      congr 1
      dsimp [b]
      push_cast
      ring
    rw [hden]
    rw [show Complex.exp (-2 * (Real.pi : Complex) *
          ((x : Complex) * n) * Complex.I) *
          (2 * Complex.exp ((A : Complex) * x) *
            (1 + Complex.exp ((b : Complex) * x))⁻¹) =
        2 * (Complex.exp (-2 * (Real.pi : Complex) *
          ((x : Complex) * n) * Complex.I) *
            Complex.exp ((A : Complex) * x)) *
              (1 + Complex.exp ((b : Complex) * x))⁻¹ by ring]
    rw [← Complex.exp_add]
    have hexponent :
        -2 * (Real.pi : Complex) * ((x : Complex) * n) * Complex.I +
            (A : Complex) * x =
          u * ((b : Complex) * x) := by
      dsimp [u, b, A]
      push_cast
      field_simp [hlam.ne', Real.pi_ne_zero]
      ring
    rw [hexponent]
    ring
  rw [show (fun x : Real =>
      Complex.exp ((-2 * Real.pi * (x * n) : Real) * Complex.I) /
        Real.cosh (Real.pi ^ 2 * x / lam)) =
      fun x => 2 * g (b * x) by
        funext x
        exact hpoint x]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.Measure.integral_comp_mul_left g b]
  rw [abs_of_pos (inv_pos.mpr hb)]
  rw [integral_cexp_mul_div_one_add_rexp u]
  have hbeta : Complex.betaIntegral u (1 - u) =
      Real.pi / Real.cosh (n * lam) := by
    convert betaIntegral_half_sub_mul_I (n * lam) using 1 <;>
      dsimp [u] <;> push_cast <;> ring
  rw [hbeta]
  rw [Complex.real_smul]
  dsimp [b, A]
  push_cast
  field_simp [hlam.ne', Real.pi_ne_zero]



def sixVertexSechProfile (lam x : Real) : Complex :=
  (Real.pi / (2 * lam) / Real.cosh (Real.pi ^ 2 * x / lam) : Real)

theorem continuous_sixVertexSechProfile
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexSechProfile lam) := by
  unfold sixVertexSechProfile
  apply Complex.continuous_ofReal.comp
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact (Real.cosh_pos _).ne'

theorem fourier_sixVertexSechProfile
    {lam : Real} (hlam : 0 < lam) (n : Real) :
    𝓕 (sixVertexSechProfile lam) n =
      (1 / (2 * Real.cosh (n * lam)) : Real) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [sixVertexSechProfile, smul_eq_mul]
  rw [show (fun x : Real =>
      Complex.exp ((-2 * Real.pi * x * n : Real) * Complex.I) *
        (Real.pi / (2 * lam) /
          Real.cosh (Real.pi ^ 2 * x / lam) : Real)) =
      fun x => (Real.pi / (2 * lam) : Real) *
        (Complex.exp ((-2 * Real.pi * (x * n) : Real) * Complex.I) /
          Real.cosh (Real.pi ^ 2 * x / lam)) by
    funext x
    push_cast
    ring]
  rw [MeasureTheory.integral_const_mul, integral_fourier_sech hlam]
  push_cast
  field_simp [hlam.ne', Real.pi_ne_zero, (Real.cosh_pos (n * lam)).ne']

theorem summable_one_div_two_cosh_nat
    {lam : Real} (hlam : 0 < lam) :
    Summable (fun n : Nat =>
      ((1 / (2 * Real.cosh ((n : Real) * lam)) : Real) : Complex)) := by
  let q := Real.exp (-lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeom : Summable (fun n : Nat => q ^ n) :=
    summable_geometric_of_lt_one hq0 hq1
  apply hgeom.of_norm_bounded
  intro n
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (mul_pos (by norm_num)
      (Real.cosh_pos ((n : Real) * lam))))]
  have hsech : 1 / Real.cosh ((n : Real) * lam) ≤
      2 * Real.exp (-((n : Real) * lam)) := by
    have hcosh : Real.exp ((n : Real) * lam) ≤
        2 * Real.cosh ((n : Real) * lam) := by
      rw [Real.cosh_eq]
      nlinarith [Real.exp_pos (-((n : Real) * lam))]
    have hhalf : 1 / (2 * Real.cosh ((n : Real) * lam)) ≤
        1 / Real.exp ((n : Real) * lam) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hcosh
    calc
      1 / Real.cosh ((n : Real) * lam) =
          2 * (1 / (2 * Real.cosh ((n : Real) * lam))) := by
        field_simp [(Real.cosh_pos _).ne']
      _ ≤ 2 * (1 / Real.exp ((n : Real) * lam)) := by gcongr
      _ = 2 * Real.exp (-((n : Real) * lam)) := by
        rw [Real.exp_neg]
        ring
  have hbound :
      1 / (2 * Real.cosh ((n : Real) * lam)) ≤
        Real.exp (-((n : Real) * lam)) := by
    have hcoshNe := (Real.cosh_pos ((n : Real) * lam)).ne'
    rw [show 1 / (2 * Real.cosh ((n : Real) * lam)) =
      (1 / Real.cosh ((n : Real) * lam)) / 2 by
        field_simp [hcoshNe]]
    linarith
  calc
    1 / (2 * Real.cosh ((n : Real) * lam)) ≤
        Real.exp (-((n : Real) * lam)) := hbound
    _ = q ^ n := by
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

theorem summable_fourier_sixVertexSechProfile_int
    {lam : Real} (hlam : 0 < lam) :
    Summable (fun n : Int =>
      FourierTransform.fourier (sixVertexSechProfile lam) (n : Real)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact (summable_one_div_two_cosh_nat hlam).congr fun n =>
      (fourier_sixVertexSechProfile hlam n).symm
  · exact (summable_one_div_two_cosh_nat hlam).congr fun n => by
      rw [fourier_sixVertexSechProfile hlam]
      have harg : ((-(n : Int) : Int) : Real) * lam =
          -((n : Real) * lam) := by
        push_cast
        ring
      rw [harg, Real.cosh_neg]

private theorem one_div_cosh_le_two_mul_exp_neg
    {x : Real} (hx : 0 ≤ x) :
    1 / Real.cosh x ≤ 2 * Real.exp (-x) := by
  have hcosh : Real.exp x ≤ 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-x)]
  have hhalf : 1 / (2 * Real.cosh x) ≤ 1 / Real.exp x :=
    one_div_le_one_div_of_le (Real.exp_pos x) hcosh
  calc
    1 / Real.cosh x = 2 * (1 / (2 * Real.cosh x)) := by
      field_simp [(Real.cosh_pos x).ne']
    _ ≤ 2 * (1 / Real.exp x) := by gcongr
    _ = 2 * Real.exp (-x) := by rw [Real.exp_neg]; ring

theorem isBigO_one_div_cosh_mul_cocompact
    {a : Real} (ha : 0 < a) :
    (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
      =O[cocompact Real] fun x : Real => |x| ^ (-2 : Real) := by
  have htopExp :
      (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
        =O[Filter.atTop] fun x : Real => Real.exp (-a * x) := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr (Real.cosh_pos (a * x)))]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    convert one_div_cosh_le_two_mul_exp_neg
      (mul_nonneg ha.le hx) using 1 <;> ring
  have htopPow :
      (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
        =O[Filter.atTop] fun x : Real => x ^ (-2 : Real) :=
    htopExp.trans (isLittleO_exp_neg_mul_rpow_atTop ha (-2)).isBigO
  have htop :
      (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
        =O[Filter.atTop] fun x : Real => |x| ^ (-2 : Real) := by
    apply htopPow.congr' EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [abs_of_nonneg hx]
  have hbot :
      (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
        =O[Filter.atBot] fun x : Real => |x| ^ (-2 : Real) := by
    have hcomp := htop.comp_tendsto tendsto_neg_atBot_atTop
    convert hcomp using 1 <;> funext x
    · simp only [Function.comp_apply]
      rw [mul_neg, Real.cosh_neg]
    · simp only [Function.comp_apply, abs_neg]
  rw [cocompact_eq_atBot_atTop, Asymptotics.isBigO_sup]
  exact ⟨hbot, htop⟩

theorem isBigO_sixVertexSechProfile_cocompact
    {lam : Real} (hlam : 0 < lam) :
    sixVertexSechProfile lam =O[cocompact Real]
      fun x : Real => |x| ^ (-2 : Real) := by
  let a : Real := Real.pi ^ 2 / lam
  have ha : 0 < a := div_pos (sq_pos_of_pos Real.pi_pos) hlam
  have hbase := isBigO_one_div_cosh_mul_cocompact ha
  have hscaled := hbase.const_mul_left
    ((Real.pi / (2 * lam) : Real) : Complex)
  apply hscaled.congr' _ EventuallyEq.rfl
  filter_upwards [] with x
  unfold sixVertexSechProfile
  dsimp [a]
  push_cast
  ring

theorem sixVertexSechProfile_poisson
    {lam : Real} (hlam : 0 < lam) (x : Real) :
    (∑' n : Int, sixVertexSechProfile lam (x + n)) =
      ∑' n : Int,
        ((1 / (2 * Real.cosh ((n : Real) * lam)) : Real) : Complex) *
          fourier n (x : UnitAddCircle) := by
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (continuous_sixVertexSechProfile hlam) one_lt_two
    (isBigO_sixVertexSechProfile_cocompact hlam)
    (summable_fourier_sixVertexSechProfile_int hlam) x
  simpa only [fourier_sixVertexSechProfile hlam] using h

private def sixVertexSechPhaseTerm
    (lam alpha : Real) (n : Int) : Complex :=
  ((1 / (2 * Real.cosh ((n : Real) * lam)) : Real) : Complex) *
    fourier n ((alpha / (2 * Real.pi) : Real) : UnitAddCircle)

private theorem summable_sixVertexSechPhaseTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (sixVertexSechPhaseTerm lam alpha) := by
  apply Summable.of_norm
  exact (summable_fourier_sixVertexSechProfile_int hlam).norm.congr fun n => by
    unfold sixVertexSechPhaseTerm
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one,
      fourier_sixVertexSechProfile hlam]

private theorem sixVertexSechPhaseTerm_pair
    (lam alpha : Real) (n : Nat) :
    sixVertexSechPhaseTerm lam alpha (Int.ofNat (n + 1)) +
        sixVertexSechPhaseTerm lam alpha (-Int.ofNat (n + 1)) =
      (sixVertexFourierRootDensityTerm lam n alpha : Complex) := by
  let m : Real := n + 1
  have hm : (m : Complex) = ((Int.ofNat (n + 1) : Int) : Complex) := by
    dsimp [m]
    norm_num
  have hphasePos :
      2 * (Real.pi : Complex) * Complex.I *
          ((Int.ofNat (n + 1) : Int) : Complex) *
            (alpha / (2 * Real.pi) : Real) =
        ((m * alpha : Real) : Complex) * Complex.I := by
    rw [← hm]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hphaseNeg :
      2 * (Real.pi : Complex) * Complex.I *
          ((-Int.ofNat (n + 1) : Int) : Complex) *
            (alpha / (2 * Real.pi) : Real) =
        -((m * alpha : Real) : Complex) * Complex.I := by
    push_cast
    rw [← hm]
    push_cast
    field_simp [Real.pi_ne_zero]
  unfold sixVertexSechPhaseTerm
  rw [fourier_coe_apply, fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one]
  rw [hphasePos, hphaseNeg]
  have hcoshNeg :
      Real.cosh (((-Int.ofNat (n + 1) : Int) : Real) * lam) =
        Real.cosh (m * lam) := by
    rw [show (((-Int.ofNat (n + 1) : Int) : Real) * lam) =
      -(m * lam) by
        dsimp [m]
        push_cast
        ring,
      Real.cosh_neg]
  rw [hcoshNeg]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  unfold sixVertexFourierRootDensityTerm
  dsimp [m]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

theorem ofReal_sixVertexFourierRootDensity_eq_tsum_phase
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    (sixVertexFourierRootDensity lam alpha : Complex) =
      ∑' n : Int, sixVertexSechPhaseTerm lam alpha n := by
  let f : Int → Complex := sixVertexSechPhaseTerm lam alpha
  have hf : Summable f := summable_sixVertexSechPhaseTerm hlam alpha
  have hinjPos : Function.Injective (fun n : PNat => (n : Int)) := by
    intro m n hmn
    exact Subtype.ext (Int.ofNat_inj.mp hmn)
  have hinjNeg : Function.Injective (fun n : PNat => -(n : Int)) := by
    intro m n hmn
    apply hinjPos
    exact neg_injective hmn
  have hpos : Summable (fun n : PNat => f (n : Int)) := by
    simpa only [Function.comp_def] using hf.comp_injective hinjPos
  have hneg : Summable (fun n : PNat => f (-(n : Int))) := by
    simpa only [Function.comp_def] using hf.comp_injective hinjNeg
  have hzero : f 0 = (1 / 2 : Complex) := by
    unfold f sixVertexSechPhaseTerm
    rw [fourier_coe_apply]
    norm_num
  let pair : PNat → Complex := fun p =>
    f (p : Int) + f (-(p : Int))
  have hpair :
      (∑' p : PNat, pair p) =
        ∑' n : Nat,
          (sixVertexFourierRootDensityTerm lam n alpha : Complex) := by
    rw [← Equiv.pnatEquivNat.tsum_eq (fun n : Nat =>
      (sixVertexFourierRootDensityTerm lam n alpha : Complex))]
    apply tsum_congr
    intro p
    dsimp [pair, f]
    simpa [Equiv.pnatEquivNat] using
      sixVertexSechPhaseTerm_pair lam alpha (Equiv.pnatEquivNat p)
  calc
    (sixVertexFourierRootDensity lam alpha : Complex) =
        (1 / 2 : Complex) +
          ∑' n : Nat,
            (sixVertexFourierRootDensityTerm lam n alpha : Complex) := by
      rw [sixVertexFourierRootDensity, Complex.ofReal_add,
        Complex.ofReal_tsum]
      congr 1
      norm_num
    _ = f 0 + ∑' p : PNat, pair p := by
      rw [hzero, hpair]
    _ = f 0 + (∑' n : PNat, f (n : Int)) +
        ∑' n : PNat, f (-(n : Int)) := by
      have hpairSum : (∑' p : PNat, pair p) =
          (∑' p : PNat, f (p : Int)) +
            ∑' p : PNat, f (-(p : Int)) := by
        dsimp [pair]
        exact hpos.tsum_add hneg
      rw [hpairSum]
      abel
    _ = ∑' n : Int, f n := by
      rw [tsum_int_eq_zero_add_tsum_pnat hf]
    _ = ∑' n : Int, sixVertexSechPhaseTerm lam alpha n := rfl

theorem summable_sixVertexSechProfile_shift
    {lam : Real} (hlam : 0 < lam) (x : Real) :
    Summable (fun n : Int => sixVertexSechProfile lam (x + n)) := by
  let f : C(Real, Complex) :=
    ⟨sixVertexSechProfile lam, continuous_sixVertexSechProfile hlam⟩
  let K : TopologicalSpace.Compacts Real :=
    ⟨{x}, isCompact_singleton⟩
  have hrestrict : Summable (fun n : Int =>
      ‖(f.comp (ContinuousMap.addRight (n : Real))).restrict K‖) := by
    apply summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    exact ((isBigO_norm_restrict_cocompact f (by norm_num)
      (isBigO_sixVertexSechProfile_cocompact hlam) K).comp_tendsto
        Int.tendsto_coe_cofinite)
  apply hrestrict.of_norm_bounded
  intro n
  exact ContinuousMap.norm_coe_le_norm
    ((f.comp (ContinuousMap.addRight (n : Real))).restrict K) ⟨x, by simp [K]⟩

theorem sixVertexFourierRootDensity_eq_tsum_sechProfile
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexFourierRootDensity lam alpha =
      ∑' n : Int,
        Real.pi / (2 * lam) /
          Real.cosh (Real.pi ^ 2 *
            (alpha / (2 * Real.pi) + n) / lam) := by
  let x : Real := alpha / (2 * Real.pi)
  let g : Int → Real := fun n =>
    Real.pi / (2 * lam) /
      Real.cosh (Real.pi ^ 2 * (x + n) / lam)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc
    (sixVertexFourierRootDensity lam alpha : Complex) =
        ∑' n : Int, sixVertexSechPhaseTerm lam alpha n :=
      ofReal_sixVertexFourierRootDensity_eq_tsum_phase hlam alpha
    _ = ∑' n : Int, sixVertexSechProfile lam (x + n) := by
      rw [sixVertexSechProfile_poisson hlam x]
      apply tsum_congr
      intro n
      rfl
    _ = ∑' n : Int, (g n : Complex) := by
      apply tsum_congr
      intro n
      rfl

theorem sixVertexFourierRootDensity_pos
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    0 < sixVertexFourierRootDensity lam alpha := by
  let x : Real := alpha / (2 * Real.pi)
  let g : Int → Real := fun n =>
    Real.pi / (2 * lam) /
      Real.cosh (Real.pi ^ 2 * (x + n) / lam)
  have hcomplex := summable_sixVertexSechProfile_shift hlam x
  have hnorm : Summable (fun n : Int => ‖g n‖) := by
    have h := hcomplex.norm
    simpa only [sixVertexSechProfile, Complex.norm_real] using h
  have hg : Summable g := Summable.of_norm hnorm
  have hnonneg (n : Int) : 0 ≤ g n := by
    dsimp [g]
    positivity
  have hzero : 0 < g 0 := by
    dsimp [g, x]
    positivity
  rw [sixVertexFourierRootDensity_eq_tsum_sechProfile hlam alpha]
  change 0 < ∑' n : Int, g n
  exact hg.tsum_pos hnonneg 0 hzero

theorem sixVertexFourierPhysicalDensity_pos
    {c : Real} (hc : 2 < c) (x : Real) :
    0 < sixVertexFourierPhysicalDensity c hc x := by
  unfold sixVertexFourierPhysicalDensity
  exact div_pos
    (sixVertexFourierRootDensity_pos
      (sixVertexAntiferroelectricLambda_pos hc) _)
    (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (sixVertexRootDensityWeight_pos hc x))

theorem sixVertexFourierPhysicalDensityFamily_pos
    {a b : Real} (ha : 2 < a) (z : Set.Icc a b × Real) :
    0 < sixVertexFourierPhysicalDensityFamily (b := b) ha z := by
  rw [sixVertexFourierPhysicalDensityFamily_apply]
  exact sixVertexFourierPhysicalDensity_pos (ha.trans_le z.1.2.1) z.2

theorem exists_uniformLower_sixVertexFourierPhysicalDensityFamily
    {a b : Real} (ha : 2 < a) (hab : a ≤ b) :
    ∃ rhoLower : Real, 0 < rhoLower ∧
      ∀ (t : Set.Icc a b) (x : Real),
        rhoLower ≤ sixVertexContinuumDensityAt
          (sixVertexFourierPhysicalDensityFamily ha) t x := by
  let X := Set.Icc a b × Set.Icc (-Real.pi) Real.pi
  let upperWeight : Set.Icc a b → Real := fun t =>
    (sixVertexAnisotropyMagnitude t.1 + 1) /
      sixVertexRootDensityScale t.1
  let proxy : X → Real := fun z =>
    sixVertexFourierRootDensity
        (sixVertexAntiferroelectricLambda z.1.1) z.2.1 /
      (2 * Real.pi * upperWeight z.1)
  let incl : X → Set.Icc a b × Real := fun z => (z.1, z.2.1)
  have hincl : Continuous incl := by
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hnum : Continuous (fun z : X =>
      sixVertexFourierRootDensity
        (sixVertexAntiferroelectricLambda z.1.1) z.2.1) := by
    have h := (continuous_sixVertexFourierRootDensity_family (b := b) ha).comp hincl
    simpa only [incl] using h
  have hupper : Continuous upperWeight := by
    have hmag : Continuous (fun t : Set.Icc a b =>
        sixVertexAnisotropyMagnitude t.1) := by
      unfold sixVertexAnisotropyMagnitude sixVertexDelta
      fun_prop
    have hscale : Continuous (fun t : Set.Icc a b =>
        sixVertexRootDensityScale t.1) := by
      unfold sixVertexRootDensityScale
      exact Real.continuous_sqrt.comp ((hmag.pow 2).sub continuous_const)
    dsimp only [upperWeight]
    apply (hmag.add continuous_const).div hscale
    · intro t
      exact (sixVertexRootDensityScale_pos
        (ha.trans_le t.2.1)).ne'
  have hproxy : Continuous proxy := by
    dsimp [proxy]
    apply hnum.div
    · exact continuous_const.mul (hupper.comp continuous_fst)
    · intro z
      have hc : 2 < z.1.1 := ha.trans_le z.1.2.1
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (div_ne_zero
          (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
          (sixVertexRootDensityScale_pos hc).ne')
  let zdefault : X :=
    (⟨a, ⟨le_rfl, hab⟩⟩,
      ⟨0, ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩⟩)
  obtain ⟨z, _hzuniv, hzmin⟩ := isCompact_univ.exists_isMinOn
    ⟨zdefault, Set.mem_univ _⟩ hproxy.continuousOn
  have hzpos : 0 < proxy z := by
    dsimp [proxy, upperWeight]
    have hc : 2 < z.1.1 := ha.trans_le z.1.2.1
    apply div_pos
    · exact sixVertexFourierRootDensity_pos
        (sixVertexAntiferroelectricLambda_pos hc) z.2.1
    · exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (div_pos
          (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
          (sixVertexRootDensityScale_pos hc))
  refine ⟨proxy z, hzpos, ?_⟩
  intro t x
  have hc : 2 < t.1 := ha.trans_le t.2.1
  let lam := sixVertexAntiferroelectricLambda t.1
  let alpha := sixVertexMomentumRapidity lam
    (sixVertexAntiferroelectricLambda_pos hc) x
  have halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [alpha]
    unfold sixVertexMomentumRapidity
    exact ((sixVertexRapidityMomentumOrderIso lam
      (sixVertexAntiferroelectricLambda_pos hc)).symm
        (Set.projIcc (-Real.pi) Real.pi
          (by linarith [Real.pi_pos]) x)).property
  let y : X := (t, ⟨alpha, halpha⟩)
  have hmin : proxy z ≤ proxy y := hzmin (Set.mem_univ y)
  refine hmin.trans ?_
  have hnumPos : 0 < sixVertexFourierRootDensity lam alpha :=
    sixVertexFourierRootDensity_pos
      (sixVertexAntiferroelectricLambda_pos hc) alpha
  have hweightPos : 0 < sixVertexRootDensityWeight t.1 x :=
    sixVertexRootDensityWeight_pos hc x
  have hweightLe := sixVertexRootDensityWeight_le hc x
  simp only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, sixVertexFourierPhysicalDensityFamily_apply]
  unfold sixVertexFourierPhysicalDensity
  change proxy y ≤
    sixVertexFourierRootDensity lam alpha /
      (2 * Real.pi * sixVertexRootDensityWeight t.1 x)
  dsimp [proxy, upperWeight, y]
  apply div_le_div_of_nonneg_left hnumPos.le
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) hweightPos)
  exact mul_le_mul_of_nonneg_left hweightLe
    (mul_nonneg (by norm_num) Real.pi_pos.le)

theorem fourier_sech
    {lam : Real} (hlam : 0 < lam) (n : Real) :
    FourierTransform.fourier (fun x : Real =>
      ((1 / Real.cosh (Real.pi ^ 2 * x / lam) : Real) : Complex)) n =
      (lam / Real.pi : Real) / Real.cosh (n * lam) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, Complex.ofReal_div, Complex.ofReal_one]
  rw [show (fun v : Real =>
      Complex.exp ((-2 * Real.pi * v * n : Real) * Complex.I) *
        (1 / (Real.cosh (Real.pi ^ 2 * v / lam) : Complex))) =
      fun v =>
        Complex.exp ((-2 * Real.pi * (v * n) : Real) * Complex.I) /
          Real.cosh (Real.pi ^ 2 * v / lam) by
    funext v
    push_cast
    ring]
  simpa only [Complex.ofReal_div] using integral_fourier_sech hlam n

end

end StatMech.FrontierD
