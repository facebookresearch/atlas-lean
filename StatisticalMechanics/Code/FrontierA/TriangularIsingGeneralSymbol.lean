/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.LogNonnegativeSinusoid
import Code.FrontierA.TriangularIsingSymbol
import Mathlib.Analysis.SpecialFunctions.Artanh









open MeasureTheory

namespace StatMech.FrontierA

noncomputable def triangularIsingInnerA
    (J1 J2 J3 k1 : Real) : Real :=
  Real.cosh (2 * J1) * Real.cosh (2 * J2) * Real.cosh (2 * J3) +
    Real.sinh (2 * J1) * Real.sinh (2 * J2) * Real.sinh (2 * J3) -
    Real.sinh (2 * J1) * Real.cos k1

noncomputable def triangularIsingInnerU
    (J2 J3 k1 : Real) : Real :=
  Real.sinh (2 * J2) + Real.sinh (2 * J3) * Real.cos k1

noncomputable def triangularIsingInnerV
    (J3 k1 : Real) : Real :=
  -Real.sinh (2 * J3) * Real.sin k1

theorem triangularIsingSymbol_eq_innerSinusoid
    (J1 J2 J3 k1 k2 : Real) :
    triangularIsingSymbol J1 J2 J3 k1 k2 =
      triangularIsingInnerA J1 J2 J3 k1 -
        triangularIsingInnerU J2 J3 k1 * Real.cos k2 -
        triangularIsingInnerV J3 k1 * Real.sin k2 := by
  unfold triangularIsingSymbol triangularIsingInnerA
    triangularIsingInnerU triangularIsingInnerV
  rw [Real.cos_add]
  ring

private theorem exp_neg_two_mul (J : Real) :
    Real.exp (-(2 * J)) = (Real.exp (2 * J))⁻¹ := by
  rw [← Real.exp_neg]

private theorem triangularIsingInnerA_exp_identity
    (J1 J2 J3 k1 : Real) :
    let a := Real.exp (2 * J1)
    let b := Real.exp (2 * J2)
    let c := Real.exp (2 * J3)
    4 * a * b * c * triangularIsingInnerA J1 J2 J3 k1 =
      a ^ 2 * b ^ 2 * c ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 +
        2 * b * c * (1 - a ^ 2) * Real.cos k1 := by
  dsimp only
  unfold triangularIsingInnerA
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq,
    Real.sinh_eq, Real.sinh_eq, Real.sinh_eq,
    exp_neg_two_mul, exp_neg_two_mul, exp_neg_two_mul]
  field_simp [Real.exp_ne_zero]
  ring

theorem triangularIsingInnerA_pos
    (J1 J2 J3 k1 : Real) :
    0 < triangularIsingInnerA J1 J2 J3 k1 := by
  let a := Real.exp (2 * J1)
  let b := Real.exp (2 * J2)
  let c := Real.exp (2 * J3)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hc : 0 < c := Real.exp_pos _
  have hxlo : -1 ≤ Real.cos k1 := Real.neg_one_le_cos k1
  have hxhi : Real.cos k1 ≤ 1 := Real.cos_le_one k1
  have hid := triangularIsingInnerA_exp_identity J1 J2 J3 k1
  dsimp only [a, b, c] at hid ⊢
  by_cases ha1 : 1 ≤ Real.exp (2 * J1)
  · have hcoeff : 2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
        (1 - Real.exp (2 * J1) ^ 2) ≤ 0 := by
      have : 1 ≤ Real.exp (2 * J1) ^ 2 := by nlinarith [Real.exp_pos (2 * J1)]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have hmul := mul_le_mul_of_nonpos_left hxhi hcoeff
    have hlowerEq :
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
            Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
            2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
              (1 - Real.exp (2 * J1) ^ 2) =
          Real.exp (2 * J1) ^ 2 *
              (Real.exp (2 * J2) * Real.exp (2 * J3) - 1) ^ 2 +
            (Real.exp (2 * J2) + Real.exp (2 * J3)) ^ 2 := by ring
    have hlowerPos : 0 <
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
            Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
            2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
              (1 - Real.exp (2 * J1) ^ 2) := by
      rw [hlowerEq]
      positivity
    have hNpos : 0 <
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
              Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
          2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
            (1 - Real.exp (2 * J1) ^ 2) * Real.cos k1 := by
      linarith
    have hfactor : 0 < 4 * Real.exp (2 * J1) * Real.exp (2 * J2) *
        Real.exp (2 * J3) := by positivity
    rw [← hid] at hNpos
    rcases mul_pos_iff.mp hNpos with h | h
    · exact h.2
    · exact (lt_asymm hfactor h.1).elim
  · have ha1' : Real.exp (2 * J1) < 1 := lt_of_not_ge ha1
    have hcoeff : 0 ≤ 2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
        (1 - Real.exp (2 * J1) ^ 2) := by
      have : Real.exp (2 * J1) ^ 2 < 1 := by nlinarith [Real.exp_pos (2 * J1)]
      positivity
    have hmul := mul_le_mul_of_nonneg_left hxlo hcoeff
    have hlowerEq :
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
            Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 -
            2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
              (1 - Real.exp (2 * J1) ^ 2) =
        Real.exp (2 * J1) ^ 2 *
            (Real.exp (2 * J2) * Real.exp (2 * J3) + 1) ^ 2 +
          (Real.exp (2 * J2) - Real.exp (2 * J3)) ^ 2 := by ring
    have hlowerPos : 0 <
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
            Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 -
            2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
              (1 - Real.exp (2 * J1) ^ 2) := by
      rw [hlowerEq]
      positivity
    have hNpos : 0 <
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
              Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
          2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
            (1 - Real.exp (2 * J1) ^ 2) * Real.cos k1 := by
      linarith
    rw [← hid] at hNpos
    have hfactor : 0 < 4 * Real.exp (2 * J1) * Real.exp (2 * J2) *
        Real.exp (2 * J3) := by positivity
    rcases mul_pos_iff.mp hNpos with h | h
    · exact h.2
    · exact (lt_asymm hfactor h.1).elim

private theorem triangularIsingInner_discriminant_exp_identity
    (J1 J2 J3 k1 : Real) :
    let a := Real.exp (2 * J1)
    let b := Real.exp (2 * J2)
    let c := Real.exp (2 * J3)
    let alpha := b * c * (a - 1) ^ 2
    let gamma := b * c * (a + 1) ^ 2
    let B := -(a ^ 2 * b ^ 2 * c ^ 2) - a ^ 2 + b ^ 2 + c ^ 2
    16 * a ^ 2 * b ^ 2 * c ^ 2 *
        (triangularIsingInnerA J1 J2 J3 k1 ^ 2 -
          (triangularIsingInnerU J2 J3 k1 ^ 2 +
            triangularIsingInnerV J3 k1 ^ 2)) =
      (B + (alpha + gamma) * Real.cos k1) ^ 2 +
        (alpha - gamma) ^ 2 * (1 - Real.cos k1 ^ 2) := by
  dsimp only
  unfold triangularIsingInnerA triangularIsingInnerU triangularIsingInnerV
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq,
    Real.sinh_eq, Real.sinh_eq, Real.sinh_eq,
    exp_neg_two_mul, exp_neg_two_mul, exp_neg_two_mul]
  have htrig := Real.sin_sq_add_cos_sq k1
  have hsin : Real.sin k1 ^ 2 = 1 - Real.cos k1 ^ 2 := by linarith
  field_simp [Real.exp_ne_zero]
  rw [hsin]
  ring

theorem triangularIsingInner_discriminant_nonneg
    (J1 J2 J3 k1 : Real) :
    0 ≤ triangularIsingInnerA J1 J2 J3 k1 ^ 2 -
      (triangularIsingInnerU J2 J3 k1 ^ 2 +
        triangularIsingInnerV J3 k1 ^ 2) := by
  let a := Real.exp (2 * J1)
  let b := Real.exp (2 * J2)
  let c := Real.exp (2 * J3)
  let alpha := b * c * (a - 1) ^ 2
  let gamma := b * c * (a + 1) ^ 2
  let B := -(a ^ 2 * b ^ 2 * c ^ 2) - a ^ 2 + b ^ 2 + c ^ 2
  have hid := triangularIsingInner_discriminant_exp_identity J1 J2 J3 k1
  dsimp only [a, b, c, alpha, gamma, B] at hid ⊢
  have hcos : 0 ≤ 1 - Real.cos k1 ^ 2 := by
    nlinarith [Real.neg_one_le_cos k1, Real.cos_le_one k1]
  have hrhs : 0 ≤
      (-(Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
              Real.exp (2 * J3) ^ 2) - Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
          (Real.exp (2 * J2) * Real.exp (2 * J3) *
                (Real.exp (2 * J1) - 1) ^ 2 +
            Real.exp (2 * J2) * Real.exp (2 * J3) *
                (Real.exp (2 * J1) + 1) ^ 2) * Real.cos k1) ^ 2 +
        (Real.exp (2 * J2) * Real.exp (2 * J3) *
              (Real.exp (2 * J1) - 1) ^ 2 -
            Real.exp (2 * J2) * Real.exp (2 * J3) *
              (Real.exp (2 * J1) + 1) ^ 2) ^ 2 *
          (1 - Real.cos k1 ^ 2) := by positivity
  have hfactor : 0 < 16 * Real.exp (2 * J1) ^ 2 *
      Real.exp (2 * J2) ^ 2 * Real.exp (2 * J3) ^ 2 := by positivity
  nlinarith


theorem triangularIsingSymbol_nonneg
    (J1 J2 J3 k1 k2 : Real) :
    0 ≤ triangularIsingSymbol J1 J2 J3 k1 k2 := by
  rw [triangularIsingSymbol_eq_innerSinusoid]
  let A := triangularIsingInnerA J1 J2 J3 k1
  let u := triangularIsingInnerU J2 J3 k1
  let v := triangularIsingInnerV J3 k1
  have hA : 0 < A := triangularIsingInnerA_pos J1 J2 J3 k1
  have hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2) :=
    triangularIsingInner_discriminant_nonneg J1 J2 J3 k1
  have hlinear : u * Real.cos k2 + v * Real.sin k2 ≤
      Real.sqrt (u ^ 2 + v ^ 2) := by
    have hcs := Real.sin_sq_add_cos_sq k2
    have hcauchy := sq_nonneg
      (u * Real.sin k2 - v * Real.cos k2)
    have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ u ^ 2 + v ^ 2)
    have hsq : (u * Real.cos k2 + v * Real.sin k2) ^ 2 ≤
        u ^ 2 + v ^ 2 := by nlinarith
    by_cases hlin : u * Real.cos k2 + v * Real.sin k2 ≤ 0
    · exact hlin.trans (Real.sqrt_nonneg _)
    · have hlinpos : 0 < u * Real.cos k2 + v * Real.sin k2 :=
        lt_of_not_ge hlin
      nlinarith [Real.sqrt_nonneg (u ^ 2 + v ^ 2)]
  have hsqrtLe : Real.sqrt (u ^ 2 + v ^ 2) ≤ A := by
    have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ u ^ 2 + v ^ 2)
    nlinarith [Real.sqrt_nonneg (u ^ 2 + v ^ 2)]
  dsimp only [A, u, v] at hlinear hsqrtLe ⊢
  linarith



theorem integral_log_triangularIsingSymbol_inner
    (J1 J2 J3 k1 : Real) :
    (∫ k2 in (-Real.pi)..Real.pi,
      Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) =
      2 * Real.pi * Real.log
        (nonnegativeSinusoidQ
          (triangularIsingInnerA J1 J2 J3 k1)
          (triangularIsingInnerU J2 J3 k1)
          (triangularIsingInnerV J3 k1) / 2) := by
  simp_rw [triangularIsingSymbol_eq_innerSinusoid]
  exact integral_log_nonnegativeSinusoid
    (triangularIsingInnerA_pos J1 J2 J3 k1)
    (triangularIsingInner_discriminant_nonneg J1 J2 J3 k1)



theorem continuous_triangularIsingFreeEnergyValue :
    Continuous (fun J : Real × Real × Real =>
      triangularIsingFreeEnergyValue J.1 J.2.1 J.2.2) := by
  let inner : (Real × Real × Real) → Real → Real := fun J k1 =>
    2 * Real.pi * Real.log
      (nonnegativeSinusoidQ
        (triangularIsingInnerA J.1 J.2.1 J.2.2 k1)
        (triangularIsingInnerU J.2.1 J.2.2 k1)
        (triangularIsingInnerV J.2.2 k1) / 2)
  have hinner : Continuous inner.uncurry := by
    apply Continuous.const_mul
    apply Continuous.log
    · unfold nonnegativeSinusoidQ triangularIsingInnerA
        triangularIsingInnerU triangularIsingInnerV
      fun_prop
    · intro p
      have hA := triangularIsingInnerA_pos p.1.1 p.1.2.1 p.1.2.2 p.2
      have hdisc := triangularIsingInner_discriminant_nonneg
        p.1.1 p.1.2.1 p.1.2.2 p.2
      exact (div_pos (nonnegativeSinusoidQ_pos hA hdisc) (by norm_num)).ne'
  have hintegral : Continuous (fun J : Real × Real × Real =>
      ∫ k1 in (-Real.pi)..Real.pi, inner J k1) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hinner (-Real.pi) Real.pi
  have hscaled : Continuous (fun J : Real × Real × Real =>
      -Real.log 2 - (1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi, inner J k1) :=
    continuous_const.sub (continuous_const.mul hintegral)
  apply hscaled.congr
  intro J
  unfold triangularIsingFreeEnergyValue
  simp_rw [integral_log_triangularIsingSymbol_inner]
  rfl

def triangularIsingZ2Sign (e : Fin 2) : Real :=
  if e = 0 then 1 else -1

noncomputable def triangularIsingCornerMomentum (e : Fin 2) : Real :=
  e.val * Real.pi

def triangularIsingCornerFactor
    (e1 e2 : Fin 2) (t1 t2 t3 : Real) : Real :=
  let s1 := triangularIsingZ2Sign e1
  let s2 := triangularIsingZ2Sign e2
  1 - s1 * t1 - s2 * t2 - s1 * s2 * t3 -
    s1 * s2 * t1 * t2 - s2 * t1 * t3 - s1 * t2 * t3 +
    t1 * t2 * t3

theorem triangularIsingHighTempSymbol_corner_eq_sq
    (J1 J2 J3 : Real) (e1 e2 : Fin 2) :
    triangularIsingHighTempSymbol J1 J2 J3
        (triangularIsingCornerMomentum e1)
        (triangularIsingCornerMomentum e2) =
      triangularIsingCornerFactor e1 e2
        (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) ^ 2 := by
  fin_cases e1 <;> fin_cases e2 <;>
    simp [triangularIsingCornerMomentum, triangularIsingCornerFactor,
      triangularIsingZ2Sign, triangularIsingHighTempSymbol,
      Real.cos_add] <;> ring

def triangularIsingCornerFactorConst
    (e1 e2 : Fin 2) (t2 t3 : Real) : Real :=
  let s1 := triangularIsingZ2Sign e1
  let s2 := triangularIsingZ2Sign e2
  1 - s2 * t2 - s1 * s2 * t3 - s1 * t2 * t3

def triangularIsingCornerFactorCoeff
    (e1 e2 : Fin 2) (t2 t3 : Real) : Real :=
  -(triangularIsingZ2Sign e1) -
    triangularIsingZ2Sign e1 * triangularIsingZ2Sign e2 * t2 -
    triangularIsingZ2Sign e2 * t3 + t2 * t3

theorem triangularIsingCornerFactor_affine
    (e1 e2 : Fin 2) (t1 t2 t3 : Real) :
    triangularIsingCornerFactor e1 e2 t1 t2 t3 =
      triangularIsingCornerFactorConst e1 e2 t2 t3 +
        t1 * triangularIsingCornerFactorCoeff e1 e2 t2 t3 := by
  unfold triangularIsingCornerFactor triangularIsingCornerFactorConst
    triangularIsingCornerFactorCoeff
  ring

theorem triangularIsingCornerFactor_const_coeff_not_both_zero
    (e1 e2 : Fin 2) (t2 t3 : Real) :
    triangularIsingCornerFactorConst e1 e2 t2 t3 ≠ 0 ∨
      triangularIsingCornerFactorCoeff e1 e2 t2 t3 ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨hconst, hcoeff⟩
  fin_cases e1 <;> fin_cases e2
  all_goals simp [triangularIsingCornerFactorConst,
    triangularIsingCornerFactorCoeff, triangularIsingZ2Sign] at hconst hcoeff
  · have hx : 2 * (t2 ^ 2 + 1) = 0 := by
      linear_combination (1 - t2) * hconst + (-t2 - 1) * hcoeff
    nlinarith [sq_nonneg t2]
  · have hx : 2 * (t2 ^ 2 + 1) = 0 := by
      linear_combination (t2 + 1) * hconst + (t2 - 1) * hcoeff
    nlinarith [sq_nonneg t2]
  · have hx : 2 * (t2 ^ 2 + 1) = 0 := by
      linear_combination -(t2 - 1) * hconst + (t2 + 1) * hcoeff
    nlinarith [sq_nonneg t2]
  · have hx : 2 * (t2 ^ 2 + 1) = 0 := by
      linear_combination (t2 + 1) * hconst - (t2 - 1) * hcoeff
    nlinarith [sq_nonneg t2]

noncomputable def triangularIsingCornerForbiddenRoot
    (e1 e2 : Fin 2) (t2 t3 : Real) : Real :=
  -triangularIsingCornerFactorConst e1 e2 t2 t3 /
    triangularIsingCornerFactorCoeff e1 e2 t2 t3

theorem triangularIsingCornerFactor_ne_zero_of_ne_forbidden
    (e1 e2 : Fin 2) (t1 t2 t3 : Real)
    (hne : t1 ≠ triangularIsingCornerForbiddenRoot e1 e2 t2 t3) :
    triangularIsingCornerFactor e1 e2 t1 t2 t3 ≠ 0 := by
  rw [triangularIsingCornerFactor_affine]
  rcases triangularIsingCornerFactor_const_coeff_not_both_zero
      e1 e2 t2 t3 with hconst | hcoeff
  · by_cases hc : triangularIsingCornerFactorCoeff e1 e2 t2 t3 = 0
    · simp [hc, hconst]
    · intro hzero
      apply hne
      unfold triangularIsingCornerForbiddenRoot
      apply (eq_div_iff hc).2
      nlinarith
  · intro hzero
    apply hne
    unfold triangularIsingCornerForbiddenRoot
    apply (eq_div_iff hcoeff).2
    nlinarith

theorem triangularIsingInner_discriminant_eq_zero_imp_cos_sq
    (J1 J2 J3 k1 : Real)
    (hzero : triangularIsingInnerA J1 J2 J3 k1 ^ 2 -
      (triangularIsingInnerU J2 J3 k1 ^ 2 +
        triangularIsingInnerV J3 k1 ^ 2) = 0) :
    Real.cos k1 ^ 2 = 1 := by
  have hid := triangularIsingInner_discriminant_exp_identity J1 J2 J3 k1
  dsimp only at hid
  rw [hzero, mul_zero] at hid
  have hcos : 0 ≤ 1 - Real.cos k1 ^ 2 := by
    nlinarith [Real.neg_one_le_cos k1, Real.cos_le_one k1]
  have hcoeff : 0 <
      (Real.exp (2 * J2) * Real.exp (2 * J3) *
            (Real.exp (2 * J1) - 1) ^ 2 -
          Real.exp (2 * J2) * Real.exp (2 * J3) *
            (Real.exp (2 * J1) + 1) ^ 2) ^ 2 := by
    have heq : Real.exp (2 * J2) * Real.exp (2 * J3) *
            (Real.exp (2 * J1) - 1) ^ 2 -
          Real.exp (2 * J2) * Real.exp (2 * J3) *
            (Real.exp (2 * J1) + 1) ^ 2 =
        -4 * Real.exp (2 * J1) * Real.exp (2 * J2) *
          Real.exp (2 * J3) := by ring
    rw [heq]
    positivity
  have hsquare : 0 ≤
      (-(Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
              Real.exp (2 * J3) ^ 2) - Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
          (Real.exp (2 * J2) * Real.exp (2 * J3) *
                (Real.exp (2 * J1) - 1) ^ 2 +
            Real.exp (2 * J2) * Real.exp (2 * J3) *
              (Real.exp (2 * J1) + 1) ^ 2) * Real.cos k1) ^ 2 :=
    sq_nonneg _
  nlinarith

theorem exists_triangularIsingCornerSign_of_cos_sq_eq_one
    {k : Real} (hcos : Real.cos k ^ 2 = 1) :
    ∃ e : Fin 2,
      Real.cos k = triangularIsingZ2Sign e ∧ Real.sin k = 0 := by
  have hsinSq : Real.sin k ^ 2 = 0 := by
    rw [Real.sin_sq, hcos]
    ring
  have hsin : Real.sin k = 0 := sq_eq_zero_iff.mp hsinSq
  rcases sq_eq_one_iff.mp hcos with h | h
  · exact ⟨0, by simp [triangularIsingZ2Sign, h, hsin]⟩
  · exact ⟨1, by simp [triangularIsingZ2Sign, h, hsin]⟩

theorem triangularIsingSymbol_zero_imp_discriminant_zero
    (J1 J2 J3 k1 k2 : Real)
    (hzero : triangularIsingSymbol J1 J2 J3 k1 k2 = 0) :
    triangularIsingInnerA J1 J2 J3 k1 ^ 2 -
      (triangularIsingInnerU J2 J3 k1 ^ 2 +
        triangularIsingInnerV J3 k1 ^ 2) = 0 := by
  let A := triangularIsingInnerA J1 J2 J3 k1
  let u := triangularIsingInnerU J2 J3 k1
  let v := triangularIsingInnerV J3 k1
  have hA : 0 < A := triangularIsingInnerA_pos J1 J2 J3 k1
  have hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2) :=
    triangularIsingInner_discriminant_nonneg J1 J2 J3 k1
  have hlinear : A = u * Real.cos k2 + v * Real.sin k2 := by
    rw [triangularIsingSymbol_eq_innerSinusoid] at hzero
    dsimp only [A, u, v]
    linarith
  have htrig := Real.sin_sq_add_cos_sq k2
  have hcauchy := sq_nonneg (u * Real.sin k2 - v * Real.cos k2)
  have hsq : (u * Real.cos k2 + v * Real.sin k2) ^ 2 ≤
      u ^ 2 + v ^ 2 := by nlinarith
  dsimp only [A, u, v] at hlinear hdisc ⊢
  nlinarith

@[simp] theorem cos_triangularIsingCornerMomentum (e : Fin 2) :
    Real.cos (triangularIsingCornerMomentum e) =
      triangularIsingZ2Sign e := by
  fin_cases e <;>
    simp [triangularIsingCornerMomentum, triangularIsingZ2Sign]

@[simp] theorem sin_triangularIsingCornerMomentum (e : Fin 2) :
    Real.sin (triangularIsingCornerMomentum e) = 0 := by
  fin_cases e <;> simp [triangularIsingCornerMomentum]



theorem exists_triangularIsingSymbol_corner_zero
    (J1 J2 J3 k1 k2 : Real)
    (hzero : triangularIsingSymbol J1 J2 J3 k1 k2 = 0) :
    ∃ e1 e2 : Fin 2,
      triangularIsingSymbol J1 J2 J3
        (triangularIsingCornerMomentum e1)
        (triangularIsingCornerMomentum e2) = 0 := by
  have hdisc := triangularIsingSymbol_zero_imp_discriminant_zero
    J1 J2 J3 k1 k2 hzero
  have hk1sq := triangularIsingInner_discriminant_eq_zero_imp_cos_sq
    J1 J2 J3 k1 hdisc
  obtain ⟨e1, hk1cos, hk1sin⟩ :=
    exists_triangularIsingCornerSign_of_cos_sq_eq_one hk1sq
  let A := triangularIsingInnerA J1 J2 J3 k1
  let u := triangularIsingInnerU J2 J3 k1
  let v := triangularIsingInnerV J3 k1
  have hv : v = 0 := by
    dsimp only [v, triangularIsingInnerV]
    rw [hk1sin]
    ring
  have hA : 0 < A := triangularIsingInnerA_pos J1 J2 J3 k1
  have hlinear : A = u * Real.cos k2 := by
    rw [triangularIsingSymbol_eq_innerSinusoid] at hzero
    dsimp only [A, u, v] at hv ⊢
    rw [hv] at hzero
    linarith
  have hdisc' : A ^ 2 - u ^ 2 = 0 := by
    dsimp only [A, u, v] at hv hdisc ⊢
    rw [hv] at hdisc
    nlinarith
  have hu : u ≠ 0 := by
    intro hu
    rw [hu, zero_mul] at hlinear
    linarith
  have hk2sq : Real.cos k2 ^ 2 = 1 := by
    rw [hlinear] at hdisc'
    nlinarith [sq_pos_of_ne_zero hu]
  obtain ⟨e2, hk2cos, hk2sin⟩ :=
    exists_triangularIsingCornerSign_of_cos_sq_eq_one hk2sq
  refine ⟨e1, e2, ?_⟩
  rw [triangularIsingSymbol] at hzero ⊢
  rw [Real.cos_add] at hzero
  rw [Real.cos_add]
  simp only [cos_triangularIsingCornerMomentum,
    sin_triangularIsingCornerMomentum, mul_zero, zero_mul, sub_zero]
  rw [hk1cos, hk2cos, hk1sin, hk2sin] at hzero
  simpa using hzero

theorem triangularIsingSymbol_pos_of_cornerFactors_ne_zero
    (J1 J2 J3 : Real)
    (hcorner : ∀ e1 e2 : Fin 2,
      triangularIsingCornerFactor e1 e2
        (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) ≠ 0) :
    ∀ k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2 := by
  intro k1 k2
  have hnonneg := triangularIsingSymbol_nonneg J1 J2 J3 k1 k2
  refine lt_of_le_of_ne hnonneg (Ne.symm ?_)
  intro hzero
  obtain ⟨e1, e2, hcornerZero⟩ :=
    exists_triangularIsingSymbol_corner_zero J1 J2 J3 k1 k2 hzero
  have hnorm := triangularIsingHighTempSymbol_mul_cosh_sq
    J1 J2 J3 (triangularIsingCornerMomentum e1)
      (triangularIsingCornerMomentum e2)
  rw [triangularIsingHighTempSymbol_corner_eq_sq, hcornerZero] at hnorm
  have hcosh : 0 <
      Real.cosh J1 ^ 2 * Real.cosh J2 ^ 2 * Real.cosh J3 ^ 2 := by positivity
  have hfactor := hcorner e1 e2
  nlinarith [sq_pos_of_ne_zero hfactor]

theorem exists_tanh_perturb_avoiding_triangularIsingCorners
    (t1 t2 t3 epsilon : Real)
    (ht1lo : -1 < t1) (ht1hi : t1 < 1) (hepsilon : 0 < epsilon) :
    ∃ t : Real,
      -1 < t ∧ t < 1 ∧ |t - t1| < epsilon ∧
        ∀ e1 e2 : Fin 2,
          t ≠ triangularIsingCornerForbiddenRoot e1 e2 t2 t3 := by
  let delta := min epsilon (min ((t1 + 1) / 2) ((1 - t1) / 2))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min hepsilon (lt_min (by linarith) (by linarith))
  let forbidden : Finset Real := Finset.univ.image fun e : Fin 2 × Fin 2 =>
    triangularIsingCornerForbiddenRoot e.1 e.2 t2 t3
  have hinfinite : (Set.Ioo (t1 - delta) (t1 + delta)).Infinite :=
    Set.infinite_coe_iff.mp (Set.Ioo.infinite (by linarith))
  have hexists : ∃ t ∈ Set.Ioo (t1 - delta) (t1 + delta), t ∉ forbidden := by
    by_contra h
    push_neg at h
    have hsubset : Set.Ioo (t1 - delta) (t1 + delta) ⊆
        (forbidden : Set Real) := by
      intro t ht
      exact h t ht
    exact hinfinite (forbidden.finite_toSet.subset hsubset)
  obtain ⟨t, ht, htforbidden⟩ := hexists
  rcases ht with ⟨htlower, htupper⟩
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · have hdle : delta ≤ (t1 + 1) / 2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  · have hdle : delta ≤ (1 - t1) / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  · rw [abs_lt]
    have hdle : delta ≤ epsilon := min_le_left _ _
    constructor <;> linarith
  · intro e1 e2 heq
    apply htforbidden
    apply Finset.mem_image.mpr
    exact ⟨(e1, e2), Finset.mem_univ _, heq.symm⟩

theorem continuousAt_artanh_of_mem_Ioo
    {t : Real} (htlo : -1 < t) (hthi : t < 1) :
    ContinuousAt Real.artanh t := by
  unfold Real.artanh
  have hden : 1 - t ≠ 0 := by linarith
  have hratio : 0 < (1 + t) / (1 - t) :=
    div_pos (by linarith) (by linarith)
  have hratioContinuous :
      ContinuousAt (fun s : Real => (1 + s) / (1 - s)) t := by
    fun_prop (disch := assumption)
  exact hratioContinuous.sqrt.log (Real.sqrt_pos.2 hratio).ne'



theorem exists_triangularIsingSymbol_pos_approx_first
    (J1 J2 J3 epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ K1 : Real, |K1 - J1| < epsilon ∧
      ∀ k1 k2, 0 < triangularIsingSymbol K1 J2 J3 k1 k2 := by
  let t1 := Real.tanh J1
  have ht1lo : -1 < t1 := Real.neg_one_lt_tanh J1
  have ht1hi : t1 < 1 := Real.tanh_lt_one J1
  have hartanh := continuousAt_artanh_of_mem_Ioo ht1lo ht1hi
  rw [Metric.continuousAt_iff] at hartanh
  obtain ⟨delta, hdelta, hclose⟩ := hartanh epsilon hepsilon
  obtain ⟨t, htlo, hthi, htclose, htavoid⟩ :=
    exists_tanh_perturb_avoiding_triangularIsingCorners
      t1 (Real.tanh J2) (Real.tanh J3) delta ht1lo ht1hi hdelta
  let K1 := Real.artanh t
  have hKclose : |K1 - J1| < epsilon := by
    have hdist := hclose (by simpa [Real.dist_eq] using htclose)
    rw [Real.dist_eq, Real.artanh_tanh] at hdist
    exact hdist
  refine ⟨K1, hKclose, ?_⟩
  apply triangularIsingSymbol_pos_of_cornerFactors_ne_zero
  intro e1 e2
  rw [show Real.tanh K1 = t by
    dsimp only [K1]
    exact Real.tanh_artanh ⟨htlo, hthi⟩]
  exact triangularIsingCornerFactor_ne_zero_of_ne_forbidden
    e1 e2 t (Real.tanh J2) (Real.tanh J3) (htavoid e1 e2)

end StatMech.FrontierA
