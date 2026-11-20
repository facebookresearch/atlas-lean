/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Polynomial.MahlerMeasure








open scoped ComplexConjugate
open MeasureTheory Polynomial

namespace StatMech.FrontierA

noncomputable def nonnegativeSinusoidQ (A u v : Real) : Real :=
  A + Real.sqrt (A ^ 2 - (u ^ 2 + v ^ 2))

noncomputable def nonnegativeSinusoidRoot (A u v : Real) : Complex :=
  (u + v * Complex.I) / nonnegativeSinusoidQ A u v

noncomputable def nonnegativeSinusoidPolynomial (A u v : Real) : Polynomial Complex :=
  let q := nonnegativeSinusoidQ A u v
  let a := nonnegativeSinusoidRoot A u v
  C ((q / 2 : Real) : Complex) *
    (X - C a) * (1 - C (conj a) * X)

theorem nonnegativeSinusoidQ_pos
    {A u v : Real} (hA : 0 < A)
    (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
    0 < nonnegativeSinusoidQ A u v := by
  unfold nonnegativeSinusoidQ
  positivity

theorem nonnegativeSinusoidRoot_norm_le_one
    {A u v : Real} (hA : 0 < A)
    (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
    ‖nonnegativeSinusoidRoot A u v‖ ≤ 1 := by
  let d := A ^ 2 - (u ^ 2 + v ^ 2)
  let q := nonnegativeSinusoidQ A u v
  have hd : 0 ≤ d := hdisc
  have hq : 0 < q := nonnegativeSinusoidQ_pos hA hdisc
  have hsqrt : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd
  have hqeq : q = A + Real.sqrt d := rfl
  have hqSq : u ^ 2 + v ^ 2 ≤ q ^ 2 := by
    rw [hqeq]
    nlinarith [Real.sqrt_nonneg d]
  have hnormSq : ‖nonnegativeSinusoidRoot A u v‖ ^ 2 =
      (u ^ 2 + v ^ 2) / q ^ 2 := by
    rw [Complex.sq_norm]
    simp [nonnegativeSinusoidRoot, q, Complex.normSq_apply]
    field_simp
  have hnormSqLe : ‖nonnegativeSinusoidRoot A u v‖ ^ 2 ≤ 1 := by
    rw [hnormSq]
    apply (div_le_one (sq_pos_of_pos hq)).2
    exact hqSq
  nlinarith [norm_nonneg (nonnegativeSinusoidRoot A u v)]

private theorem nonnegativeSinusoid_secondFactor_logMahler
    (a : Complex) (ha : ‖a‖ ≤ 1) :
    (1 - C (conj a) * X : Polynomial Complex).logMahlerMeasure = 0 := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hconj : conj a ≠ 0 := by simpa using ha0
  rw [show (1 - C (conj a) * X : Polynomial Complex) =
      C (-conj a) * X + C 1 by
        calc
          1 - C (conj a) * X = C 1 + -(C (conj a) * X) := by
            rw [map_one]
            rfl
          _ = C 1 + C (-conj a) * X := by
            rw [map_neg, neg_mul]
          _ = C (-conj a) * X + C 1 := add_comm _ _]
  rw [Polynomial.logMahlerMeasure_eq_log_MahlerMeasure,
    Polynomial.mahlerMeasure_C_mul_X_add_C (neg_ne_zero.mpr hconj)]
  simp only [norm_neg, Complex.norm_conj, norm_one]
  rw [max_eq_right ha]
  simp

theorem nonnegativeSinusoidPolynomial_logMahler
    {A u v : Real} (hA : 0 < A)
    (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
    (nonnegativeSinusoidPolynomial A u v).logMahlerMeasure =
      Real.log (nonnegativeSinusoidQ A u v / 2) := by
  let q := nonnegativeSinusoidQ A u v
  let a := nonnegativeSinusoidRoot A u v
  have hq : 0 < q := nonnegativeSinusoidQ_pos hA hdisc
  have hq2 : (q / 2 : Real) ≠ 0 := (div_pos hq (by norm_num)).ne'
  have hfirst : (X - C a : Polynomial Complex) ≠ 0 := by
    exact X_sub_C_ne_zero a
  have hsecond : (1 - C (conj a) * X : Polynomial Complex) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun p : Polynomial Complex => p.coeff 0) h
    simp at hcoeff
  have ha : ‖a‖ ≤ 1 := nonnegativeSinusoidRoot_norm_le_one hA hdisc
  unfold nonnegativeSinusoidPolynomial
  dsimp only
  change
    (C ((q / 2 : Real) : Complex) * (X - C a) *
      (1 - C (conj a) * X)).logMahlerMeasure = Real.log (q / 2)
  rw [mul_assoc]
  rw [Polynomial.logMahlerMeasure_C_mul (by exact_mod_cast hq2)
      (mul_ne_zero hfirst hsecond),
    Polynomial.logMahlerMeasure_mul_eq_add_logMahlerMeasure
      (mul_ne_zero hfirst hsecond),
    Polynomial.logMahlerMeasure_X_sub_C,
    nonnegativeSinusoid_secondFactor_logMahler a ha]
  have hposLog : ‖a‖.posLog = 0 :=
    (Real.posLog_eq_zero_iff ‖a‖).2 (by simpa using ha)
  rw [hposLog]
  have hq2pos : 0 < q / 2 := by positivity
  simp only [add_zero, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos hq2pos]

theorem norm_eval_nonnegativeSinusoidPolynomial
    {A u v : Real} (hA : 0 < A)
    (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2))
    {z : Complex} (hz : ‖z‖ = 1) :
    ‖eval z (nonnegativeSinusoidPolynomial A u v)‖ =
      A - u * z.re - v * z.im := by
  let d := A ^ 2 - (u ^ 2 + v ^ 2)
  let q := nonnegativeSinusoidQ A u v
  let a := nonnegativeSinusoidRoot A u v
  have hd : 0 ≤ d := hdisc
  have hq : 0 < q := nonnegativeSinusoidQ_pos hA hdisc
  have hqne : (q : Complex) ≠ 0 := by exact_mod_cast hq.ne'
  have hsqrt : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd
  have hqeq : q = A + Real.sqrt d := rfl
  have hqidentity : q ^ 2 + (u ^ 2 + v ^ 2) = 2 * A * q := by
    rw [hqeq]
    nlinarith
  have hnormSqZ : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz]
    norm_num
  have hmulConj : z * conj z = 1 := by
    rw [Complex.mul_conj, hnormSqZ]
    norm_num
  have hfactor : 1 - conj a * z = z * conj (z - a) := by
    calc
      1 - conj a * z = z * conj z - conj a * z := by rw [hmulConj]
      _ = z * (conj z - conj a) := by ring
      _ = z * conj (z - a) := by rw [map_sub]
  have hfactorNorm : ‖1 - conj a * z‖ = ‖z - a‖ := by
    rw [hfactor, norm_mul, hz, one_mul, Complex.norm_conj]
  have haRe : a.re = u / q := by
    dsimp only [q]
    simp [a, nonnegativeSinusoidRoot, Complex.div_re, hq.ne']
    field_simp
  have haIm : a.im = v / q := by
    dsimp only [q]
    simp [a, nonnegativeSinusoidRoot, Complex.div_im, hq.ne']
    field_simp
  have hnormDiff : ‖z - a‖ ^ 2 =
      1 + (u ^ 2 + v ^ 2) / q ^ 2 -
        2 * (u * z.re + v * z.im) / q := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change (z.re - a.re) * (z.re - a.re) +
        (z.im - a.im) * (z.im - a.im) = _
    rw [haRe, haIm]
    have hzcoords : z.re ^ 2 + z.im ^ 2 = 1 := by
      rw [Complex.normSq_apply] at hnormSqZ
      nlinarith
    field_simp
    nlinarith
  unfold nonnegativeSinusoidPolynomial
  dsimp only
  simp only [eval_mul, eval_C, eval_sub, eval_X, eval_one, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  rw [hfactorNorm]
  change |q / 2| * ‖z - a‖ * ‖z - a‖ = _
  rw [abs_of_pos (by positivity : 0 < q / 2)]
  rw [show q / 2 * ‖z - a‖ * ‖z - a‖ =
      q / 2 * ‖z - a‖ ^ 2 by ring, hnormDiff]
  field_simp
  nlinarith



theorem circleAverage_log_nonnegativeSinusoid
    {A u v : Real} (hA : 0 < A)
    (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
    Real.circleAverage
        (fun z : Complex => Real.log (A - u * z.re - v * z.im)) 0 1 =
      Real.log (nonnegativeSinusoidQ A u v / 2) := by
  rw [← nonnegativeSinusoidPolynomial_logMahler hA hdisc,
    Polynomial.logMahlerMeasure_def]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hnorm : ‖z‖ = 1 := by simpa using hz
  change Real.log (A - u * z.re - v * z.im) =
    Real.log ‖eval z (nonnegativeSinusoidPolynomial A u v)‖
  rw [norm_eval_nonnegativeSinusoidPolynomial hA hdisc hnorm]

theorem integral_log_nonnegativeSinusoid_zero_two_pi
    {A u v : Real} (hA : 0 < A)
    (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
    (∫ theta in (0 : Real)..(2 * Real.pi),
        Real.log (A - u * Real.cos theta - v * Real.sin theta)) =
      2 * Real.pi * Real.log (nonnegativeSinusoidQ A u v / 2) := by
  have hcircle := circleAverage_log_nonnegativeSinusoid hA hdisc
  rw [Real.circleAverage_def] at hcircle
  have hre (theta : Real) : (circleMap 0 1 theta).re = Real.cos theta := by
    simp [circleMap, Complex.exp_mul_I, Complex.cos_ofReal_re]
  have him (theta : Real) : (circleMap 0 1 theta).im = Real.sin theta := by
    simp [circleMap, Complex.exp_mul_I, Complex.sin_ofReal_re]
  simp_rw [hre, him] at hcircle
  simp only [smul_eq_mul] at hcircle
  have hpi : (2 * Real.pi : Real) ≠ 0 := by positivity
  calc
    (∫ theta in (0 : Real)..(2 * Real.pi),
        Real.log (A - u * Real.cos theta - v * Real.sin theta)) =
        (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
          ∫ theta in (0 : Real)..(2 * Real.pi),
            Real.log (A - u * Real.cos theta - v * Real.sin theta)) := by
      field_simp
    _ = 2 * Real.pi * Real.log (nonnegativeSinusoidQ A u v / 2) := by
      rw [hcircle]

theorem integral_log_nonnegativeSinusoid
    {A u v : Real} (hA : 0 < A)
    (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
    (∫ theta in (-Real.pi)..Real.pi,
        Real.log (A - u * Real.cos theta - v * Real.sin theta)) =
      2 * Real.pi * Real.log (nonnegativeSinusoidQ A u v / 2) := by
  let f : Real → Real := fun theta =>
    Real.log (A - u * Real.cos theta - v * Real.sin theta)
  have hperiodic : Function.Periodic f (2 * Real.pi) := by
    intro theta
    dsimp only [f]
    rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hshift := hperiodic.intervalIntegral_add_eq 0 (-Real.pi)
  calc
    (∫ theta in (-Real.pi)..Real.pi,
        Real.log (A - u * Real.cos theta - v * Real.sin theta)) =
        ∫ theta in (0 : Real)..(2 * Real.pi),
          Real.log (A - u * Real.cos theta - v * Real.sin theta) := by
      convert hshift.symm using 1 <;> dsimp only [f] <;> ring
    _ = _ := integral_log_nonnegativeSinusoid_zero_two_pi hA hdisc

end StatMech.FrontierA
