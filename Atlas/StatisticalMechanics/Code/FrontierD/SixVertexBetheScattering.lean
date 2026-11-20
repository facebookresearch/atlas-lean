/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheEquations
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Finset

namespace StatMech.FrontierD

noncomputable section

private theorem exp_neg_two_arctan_mul_I (r : ℝ) :
    Complex.exp (((-2 * Real.arctan r : ℝ) : ℂ) * Complex.I) =
      ((1 : ℂ) - (r : ℂ) * Complex.I) /
        ((1 : ℂ) + (r : ℂ) * Complex.I) := by
  have hsqrt : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hsquare : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hcos : Real.cos (-2 * Real.arctan r) =
      (1 - r ^ 2) / (1 + r ^ 2) := by
    rw [show -2 * Real.arctan r = -(2 * Real.arctan r) by ring]
    rw [Real.cos_neg, Real.cos_two_mul, Real.cos_arctan]
    field_simp
    rw [hsquare]
    ring
  have hsin : Real.sin (-2 * Real.arctan r) =
      (-2 * r) / (1 + r ^ 2) := by
    rw [show -2 * Real.arctan r = -(2 * Real.arctan r) by ring]
    rw [Real.sin_neg, Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
    field_simp
    rw [hsquare]
  rw [Complex.exp_ofReal_mul_I, hcos, hsin]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
      Complex.one_re, Complex.ofReal_re, Complex.I_re, Complex.add_im,
      Complex.sub_im, Complex.mul_im, Complex.div_im, Complex.one_im,
      Complex.ofReal_im, Complex.I_im, Complex.normSq_apply, mul_zero,
      mul_one, zero_add, add_zero, sub_zero, zero_sub]
  all_goals
    field_simp
    ring



noncomputable def sixVertexScatteringDenominator (c x y : ℝ) : ℂ :=
  Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * y) -
    2 * sixVertexDelta c

theorem sixVertexScatteringDenominator_eq (c x y : ℝ) :
    sixVertexScatteringDenominator c x y =
      (sixVertexThetaDenominator c x y : ℂ) +
        (Real.sin x - Real.sin y : ℝ) * Complex.I := by
  unfold sixVertexScatteringDenominator sixVertexThetaDenominator
  rw [mul_comm Complex.I (x : ℂ), Complex.exp_ofReal_mul_I]
  rw [show -Complex.I * (y : ℂ) = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem sixVertexScatteringDenominator_ne_zero {c : ℝ} (hc : 2 < c)
    (x y : ℝ) : sixVertexScatteringDenominator c x y ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [sixVertexScatteringDenominator_eq] at hre
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.zero_re] at hre
  exact (sixVertexThetaDenominator_pos hc x y).ne' hre



theorem sixVertexTheta_exp_identity {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    Complex.exp (-Complex.I * sixVertexTheta c x y) =
      Complex.exp (Complex.I * (x - y)) *
        star (sixVertexScatteringDenominator c x y) /
          sixVertexScatteringDenominator c x y := by
  let a := sixVertexThetaDenominator c x y
  let b := Real.sin x - Real.sin y
  have ha : 0 < a := sixVertexThetaDenominator_pos hc x y
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hphase :
      Complex.exp (((-2 * Real.arctan (b / a) : ℝ) : ℂ) * Complex.I) =
        ((a : ℂ) - (b : ℂ) * Complex.I) /
          ((a : ℂ) + (b : ℂ) * Complex.I) := by
    rw [exp_neg_two_arctan_mul_I]
    push_cast
    field_simp
  have hden : sixVertexScatteringDenominator c x y =
      (a : ℂ) + (b : ℂ) * Complex.I := by
    exact sixVertexScatteringDenominator_eq c x y
  have hstar : star (sixVertexScatteringDenominator c x y) =
      (a : ℂ) - (b : ℂ) * Complex.I := by
    rw [hden]
    apply Complex.ext <;> simp
  rw [sixVertexTheta]
  change Complex.exp (-Complex.I *
      (((y - x + 2 * Real.arctan (b / a) : ℝ) : ℂ))) = _
  rw [show -Complex.I * (((y - x + 2 * Real.arctan (b / a) : ℝ) : ℂ)) =
      Complex.I * ((x - y : ℝ) : ℂ) +
        (((-2 * Real.arctan (b / a) : ℝ) : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [Complex.exp_add, hphase, hstar, hden]
  push_cast
  ring


def SixVertexSatisfiesMultiplicativeBetheEquations
    (c : ℝ) (N n : ℕ) (p : Fin n → ℝ) : Prop :=
  ∀ j, Complex.exp (Complex.I * ((N : ℝ) * p j)) =
    (-1 : ℂ) ^ (n - 1) *
      Complex.exp (-Complex.I * ∑ k, sixVertexTheta c (p j) (p k))

theorem exp_two_pi_mul_centralQuantumNumber {n : ℕ} (j : Fin n) :
    Complex.exp (Complex.I *
      (2 * Real.pi * sixVertexCentralQuantumNumber j)) =
        (-1 : ℂ) ^ (n - 1) := by
  have hquantum :
      2 * Real.pi * sixVertexCentralQuantumNumber j =
        2 * Real.pi * (j.val : ℝ) - (n - 1 : ℕ) * Real.pi := by
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      exact Fin.elim0 j
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    rw [Nat.cast_sub hn]
    simp [sixVertexCentralQuantumNumber]
    ring
  have hquantumc :
      (2 : ℂ) * (Real.pi : ℂ) *
          (sixVertexCentralQuantumNumber j : ℂ) =
        (2 : ℂ) * (Real.pi : ℂ) * (j.val : ℂ) -
          (((n - 1 : ℕ) : ℝ) : ℂ) * (Real.pi : ℂ) := by
    have hc := congrArg (fun z : ℝ => (z : ℂ)) hquantum
    push_cast at hc
    exact hc
  rw [hquantumc]
  have hsplit :
      Complex.I *
          ((2 : ℂ) * (Real.pi : ℂ) * (j.val : ℂ) -
            (((n - 1 : ℕ) : ℝ) : ℂ) * (Real.pi : ℂ)) =
        ((j.val : ℂ) * (2 * Real.pi * Complex.I)) +
          (((-((n - 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  rw [Complex.exp_nat_mul_two_pi_mul_I]
  simp only [one_mul]
  rw [Complex.exp_ofReal_mul_I,
    show -((n - 1 : ℕ) : ℝ) * Real.pi =
      -(((n - 1 : ℕ) : ℝ) * Real.pi) by ring,
    Real.cos_neg, Real.sin_neg,
    Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  norm_num



theorem SixVertexSatisfiesBetheEquations.multiplicative
    {c : ℝ} {N n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexSatisfiesBetheEquations c N n p) :
    SixVertexSatisfiesMultiplicativeBetheEquations c N n p := by
  intro j
  have hj := hp j
  have harg :
      Complex.I * (((N : ℝ) : ℂ) * (p j : ℂ)) =
        Complex.I * ((2 : ℂ) * (Real.pi : ℂ) *
            (sixVertexCentralQuantumNumber j : ℂ)) +
          (-Complex.I *
            ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ)) := by
    calc
      _ = Complex.I * (((N : ℝ) * p j : ℝ) : ℂ) := by
        push_cast
        ring
      _ = Complex.I *
          ((2 * Real.pi * sixVertexCentralQuantumNumber j -
            ∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ) := by
              congr 1
              exact_mod_cast hj
      _ = _ := by
        push_cast
        ring
  rw [harg, Complex.exp_add, exp_two_pi_mul_centralQuantumNumber]

theorem exp_neg_I_sum_sixVertexTheta_eq_product
    {c : ℝ} (hc : 2 < c) {n : ℕ} (p : Fin n → ℝ) (j : Fin n) :
    Complex.exp (-Complex.I * ∑ k, sixVertexTheta c (p j) (p k)) =
      ∏ k, Complex.exp (Complex.I * (p j - p k)) *
        star (sixVertexScatteringDenominator c (p j) (p k)) /
          sixVertexScatteringDenominator c (p j) (p k) := by
  have hsum :
      -Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ) =
        ∑ k, -Complex.I * sixVertexTheta c (p j) (p k) := by
    push_cast
    rw [Finset.mul_sum]
  rw [hsum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro k _
  exact sixVertexTheta_exp_identity hc (p j) (p k)

end

end StatMech.FrontierD
