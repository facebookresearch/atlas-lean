/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRapidityMomentum





namespace StatMech.FrontierD

noncomputable section


def sixVertexRapidityCircle (lam alpha : Real) : Complex :=
  (((Real.cosh lam * Real.cos alpha - 1 : Real) : Complex) +
    ((Real.sinh lam * Real.sin alpha : Real) : Complex) * Complex.I) /
      ((Real.cosh lam - Real.cos alpha : Real) : Complex)


def sixVertexMomentumCircle (lam alpha : Real) : Complex :=
  Complex.exp
    ((sixVertexRapidityMomentum lam alpha : Complex) * Complex.I)

theorem hasDerivAt_sixVertexRapidityCircle
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexRapidityCircle lam)
      (((sixVertexXiFourier lam alpha : Real) : Complex) * Complex.I *
        sixVertexRapidityCircle lam alpha) alpha := by
  let d := Real.cosh lam
  let s := Real.sinh lam
  have hdenPos : 0 < d - Real.cos alpha := by
    dsimp [d]
    have hd : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  have hden : ((d - Real.cos alpha : Real) : Complex) ≠ 0 := by
    exact_mod_cast hdenPos.ne'
  have hre : HasDerivAt
      (fun a : Real => d * Real.cos a - 1)
      (-d * Real.sin alpha) alpha := by
    convert (Real.hasDerivAt_cos alpha).const_mul d |>.sub_const 1 using 1
    ring
  have him : HasDerivAt
      (fun a : Real => s * Real.sin a)
      (s * Real.cos alpha) alpha := by
    convert (Real.hasDerivAt_sin alpha).const_mul s using 1
  have hnum := hre.ofReal_comp.add (him.ofReal_comp.mul_const Complex.I)
  have hdenDeriv : HasDerivAt
      (fun a : Real => ((d - Real.cos a : Real) : Complex))
      (Real.sin alpha : Complex) alpha := by
    convert ((Real.hasDerivAt_cos alpha).const_sub d).ofReal_comp using 1
    ring
  have hquot := hnum.div hdenDeriv hden
  convert hquot using 1
  rw [sixVertexXiFourier_eq hlam]
  change (((s / (d - Real.cos alpha) : Real) : Complex) * Complex.I) *
      sixVertexRapidityCircle lam alpha =
    ((((-d * Real.sin alpha : Real) : Complex) +
          ((s * Real.cos alpha : Real) : Complex) * Complex.I) *
          ((d - Real.cos alpha : Real) : Complex) -
        ((((d * Real.cos alpha - 1 : Real) : Complex) +
            ((s * Real.sin alpha : Real) : Complex) * Complex.I) *
          (Real.sin alpha : Complex))) /
        ((d - Real.cos alpha : Real) : Complex) ^ 2
  rw [sixVertexRapidityCircle]
  dsimp [d, s]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_one]
  have hdenC :
      (Real.cosh lam : Complex) - (Real.cos alpha : Complex) ≠ 0 := by
    simpa only [Complex.ofReal_sub] using hden
  field_simp [hdenC]
  have hh : Real.cosh lam ^ 2 - Real.sinh lam ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq lam
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.sinh_ofReal_re,
      Complex.sin_ofReal_re, Complex.cos_ofReal_re]
    linear_combination Real.sin alpha * hh
  · simp [Complex.mul_re, Complex.mul_im, Complex.sinh_ofReal_re,
      Complex.sin_ofReal_re, Complex.cos_ofReal_re]
    linear_combination Real.sinh lam * (Real.sin_sq_add_cos_sq alpha)

theorem hasDerivAt_sixVertexMomentumCircle
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexMomentumCircle lam)
      (((sixVertexXiFourier lam alpha : Real) : Complex) * Complex.I *
        sixVertexMomentumCircle lam alpha) alpha := by
  unfold sixVertexMomentumCircle
  have hk := hasDerivAt_sixVertexRapidityMomentum hlam alpha
  have hinner := hk.ofReal_comp.mul_const Complex.I
  have houter := Complex.hasDerivAt_exp
    ((sixVertexRapidityMomentum lam alpha : Complex) * Complex.I)
  have hcomp := houter.comp alpha hinner
  change HasDerivAt
    (fun a => Complex.exp
      ((sixVertexRapidityMomentum lam a : Complex) * Complex.I)) _ alpha
  simpa only [Function.comp_apply, mul_comm] using hcomp

theorem sixVertexRapidityCircle_ne_zero
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexRapidityCircle lam alpha ≠ 0 := by
  let d := Real.cosh lam
  let s := Real.sinh lam
  have hd : 1 < d := by
    dsimp [d]
    exact Real.one_lt_cosh.mpr hlam.ne'
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sinh_pos_iff.mpr hlam
  have hdenPos : 0 < d - Real.cos alpha := by
    linarith [Real.cos_le_one alpha]
  have hden : ((d - Real.cos alpha : Real) : Complex) ≠ 0 := by
    exact_mod_cast hdenPos.ne'
  intro hv
  have hnum :
      (((d * Real.cos alpha - 1 : Real) : Complex) +
        ((s * Real.sin alpha : Real) : Complex) * Complex.I) = 0 := by
    rw [sixVertexRapidityCircle] at hv
    exact (div_eq_zero_iff.mp hv).resolve_right hden
  have hre := congrArg Complex.re hnum
  have him := congrArg Complex.im hnum
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re] at hre him
  have hsin : Real.sin alpha = 0 := him.resolve_left hs.ne'
  have hcosSq : Real.cos alpha ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  rcases sq_eq_one_iff.mp hcosSq with hcos | hcos <;> nlinarith

private def sixVertexCircleRatio (lam alpha : Real) : Complex :=
  sixVertexMomentumCircle lam alpha / sixVertexRapidityCircle lam alpha

private theorem hasDerivAt_sixVertexCircleRatio
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexCircleRatio lam) 0 alpha := by
  have hu := hasDerivAt_sixVertexMomentumCircle hlam alpha
  have hv := hasDerivAt_sixVertexRapidityCircle hlam alpha
  have hv0 := sixVertexRapidityCircle_ne_zero hlam alpha
  have hdiv := hu.div hv hv0
  convert hdiv using 1
  ring


theorem sixVertexMomentumCircle_eq_rapidityCircle
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexMomentumCircle lam alpha =
      sixVertexRapidityCircle lam alpha := by
  have hw (x : Real) : HasDerivAt (sixVertexCircleRatio lam) 0 x :=
    hasDerivAt_sixVertexCircleRatio hlam x
  have hw0 : sixVertexCircleRatio lam 0 = 1 := by
    unfold sixVertexCircleRatio sixVertexMomentumCircle
      sixVertexRapidityCircle sixVertexRapidityMomentum
    have hden : Real.cosh lam - 1 ≠ 0 := by
      have hcosh := Real.one_lt_cosh.mpr hlam.ne'
      linarith
    have hdenC : Complex.cosh (lam : Complex) - 1 ≠ 0 := by
      rw [<- Complex.ofReal_cosh]
      exact_mod_cast hden
    simp [hdenC]
  have hwa : sixVertexCircleRatio lam alpha =
      sixVertexCircleRatio lam 0 := by
    by_cases ha : 0 <= alpha
    · have hcont : ContinuousOn (sixVertexCircleRatio lam)
          (Set.Icc 0 alpha) :=
        fun x _ => (hw x).continuousAt.continuousWithinAt
      exact constant_of_has_deriv_right_zero hcont
        (fun x _ => (hw x).hasDerivWithinAt) alpha ⟨ha, le_rfl⟩
    · have ha' : alpha <= 0 := le_of_not_ge ha
      have hcont : ContinuousOn (sixVertexCircleRatio lam)
          (Set.Icc alpha 0) :=
        fun x _ => (hw x).continuousAt.continuousWithinAt
      exact (constant_of_has_deriv_right_zero hcont
        (fun x _ => (hw x).hasDerivWithinAt) 0 ⟨ha', le_rfl⟩).symm
  have hwone : sixVertexCircleRatio lam alpha = 1 := hwa.trans hw0
  exact (div_eq_one_iff_eq (sixVertexRapidityCircle_ne_zero hlam alpha)).mp
    hwone

theorem cos_sixVertexRapidityMomentum
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Real.cos (sixVertexRapidityMomentum lam alpha) =
      (Real.cosh lam * Real.cos alpha - 1) /
        (Real.cosh lam - Real.cos alpha) := by
  have huv := sixVertexMomentumCircle_eq_rapidityCircle hlam alpha
  have hre := congrArg Complex.re huv
  unfold sixVertexMomentumCircle sixVertexRapidityCircle at hre
  simp [Complex.exp_ofReal_mul_I_re, Complex.div_re,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re] at hre
  have hden : Real.cosh lam - Real.cos alpha ≠ 0 := by
    have hd := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  field_simp [hden] at hre ⊢
  nlinarith

theorem sin_sixVertexRapidityMomentum
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Real.sin (sixVertexRapidityMomentum lam alpha) =
      Real.sinh lam * Real.sin alpha /
        (Real.cosh lam - Real.cos alpha) := by
  have huv := sixVertexMomentumCircle_eq_rapidityCircle hlam alpha
  have him := congrArg Complex.im huv
  unfold sixVertexMomentumCircle sixVertexRapidityCircle at him
  simp [Complex.exp_ofReal_mul_I_im, Complex.div_im,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.sinh_ofReal_re] at him
  have hden : Real.cosh lam - Real.cos alpha ≠ 0 := by
    have hd := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  field_simp [hden] at him ⊢
  nlinarith

end

end StatMech.FrontierD
