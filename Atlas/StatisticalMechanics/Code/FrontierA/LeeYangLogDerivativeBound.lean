/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.LeeYangFieldAnalytic
import Mathlib.Algebra.Polynomial.Splits

open scoped BigOperators
open Polynomial

namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangFugacityLogDerivative_norm_le_openUnitDisk
    {beta : ℝ} (hbeta : 0 ≤ beta) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖leeYangFugacityLogDerivative G beta z‖ ≤
      (Fintype.card V : ℝ) / (1 - ‖z‖) := by
  let p : ℂ[X] := leeYangComplexPolynomial G beta
  have hp : p ≠ 0 := leeYangComplexPolynomial_ne_zero G beta
  have hpz : p.eval z ≠ 0 :=
    leeYangComplexPolynomial_ne_zero_of_norm_ne_one G hbeta (ne_of_lt hz)
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hroot : ∀ r ∈ p.roots, ‖r‖ = 1 := by
    intro r hr
    apply finiteGraph_hasLeeYangCircle G hbeta r
    exact (Polynomial.mem_roots hp).mp hr
  have hterm : ∀ r ∈ p.roots,
      ‖1 / (z - r)‖ ≤ 1 / (1 - ‖z‖) := by
    intro r hr
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le (sub_pos.mpr hz)
    calc
      1 - ‖z‖ = ‖r‖ - ‖z‖ := by rw [hroot r hr]
      _ ≤ ‖r - z‖ := norm_sub_norm_le r z
      _ = ‖z - r‖ := norm_sub_rev r z
  have hsum : ∀ R : Multiset ℂ,
      (∀ r ∈ R, ‖1 / (z - r)‖ ≤ 1 / (1 - ‖z‖)) →
      ‖(R.map (fun r => 1 / (z - r))).sum‖ ≤
        (R.card : ℝ) * (1 / (1 - ‖z‖)) := by
    intro R
    induction R using Multiset.induction_on with
    | empty => simp
    | cons r R ih =>
        intro hR
        have hr := hR r (by simp)
        have htail : ∀ x ∈ R, ‖1 / (z - x)‖ ≤ 1 / (1 - ‖z‖) := by
          intro x hx
          exact hR x (by simp [hx])
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          Nat.cast_add, Nat.cast_one]
        calc
          ‖1 / (z - r) + (Multiset.map (fun x => 1 / (z - x)) R).sum‖ ≤
              ‖1 / (z - r)‖ +
                ‖(Multiset.map (fun x => 1 / (z - x)) R).sum‖ := norm_add_le _ _
          _ ≤ 1 / (1 - ‖z‖) +
                (R.card : ℝ) * (1 / (1 - ‖z‖)) :=
            add_le_add hr (ih htail)
          _ = ((R.card : ℝ) + 1) * (1 / (1 - ‖z‖)) := by ring
  rw [leeYangFugacityLogDerivative]
  rw [hsplits.eval_derivative_div_eval_of_ne_zero hpz]
  calc
    ‖(Multiset.map (fun r => 1 / (z - r)) p.roots).sum‖ ≤
        (p.roots.card : ℝ) * (1 / (1 - ‖z‖)) := hsum p.roots hterm
    _ = (Fintype.card V : ℝ) / (1 - ‖z‖) := by
      rw [← hsplits.natDegree_eq_card_roots,
        leeYangComplexPolynomial_natDegree]
      ring

theorem leeYangFugacityLogDerivative_norm_le_exterior
    {beta : ℝ} (hbeta : 0 ≤ beta) {z : ℂ} (hz : 1 < ‖z‖) :
    ‖leeYangFugacityLogDerivative G beta z‖ ≤
      (Fintype.card V : ℝ) / (‖z‖ - 1) := by
  let p : ℂ[X] := leeYangComplexPolynomial G beta
  have hp : p ≠ 0 := leeYangComplexPolynomial_ne_zero G beta
  have hpz : p.eval z ≠ 0 :=
    leeYangComplexPolynomial_ne_zero_of_norm_ne_one G hbeta (ne_of_gt hz)
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hroot : ∀ r ∈ p.roots, ‖r‖ = 1 := by
    intro r hr
    apply finiteGraph_hasLeeYangCircle G hbeta r
    exact (Polynomial.mem_roots hp).mp hr
  have hterm : ∀ r ∈ p.roots,
      ‖1 / (z - r)‖ ≤ 1 / (‖z‖ - 1) := by
    intro r hr
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le (sub_pos.mpr hz)
    calc
      ‖z‖ - 1 = ‖z‖ - ‖r‖ := by rw [hroot r hr]
      _ ≤ ‖z - r‖ := norm_sub_norm_le z r
  have hsum : ∀ R : Multiset ℂ,
      (∀ r ∈ R, ‖1 / (z - r)‖ ≤ 1 / (‖z‖ - 1)) →
      ‖(R.map (fun r => 1 / (z - r))).sum‖ ≤
        (R.card : ℝ) * (1 / (‖z‖ - 1)) := by
    intro R
    induction R using Multiset.induction_on with
    | empty => simp
    | cons r R ih =>
        intro hR
        have hr := hR r (by simp)
        have htail : ∀ x ∈ R, ‖1 / (z - x)‖ ≤ 1 / (‖z‖ - 1) := by
          intro x hx
          exact hR x (by simp [hx])
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          Nat.cast_add, Nat.cast_one]
        calc
          ‖1 / (z - r) + (Multiset.map (fun x => 1 / (z - x)) R).sum‖ ≤
              ‖1 / (z - r)‖ +
                ‖(Multiset.map (fun x => 1 / (z - x)) R).sum‖ := norm_add_le _ _
          _ ≤ 1 / (‖z‖ - 1) +
                (R.card : ℝ) * (1 / (‖z‖ - 1)) :=
            add_le_add hr (ih htail)
          _ = ((R.card : ℝ) + 1) * (1 / (‖z‖ - 1)) := by ring
  rw [leeYangFugacityLogDerivative]
  rw [hsplits.eval_derivative_div_eval_of_ne_zero hpz]
  calc
    ‖(Multiset.map (fun r => 1 / (z - r)) p.roots).sum‖ ≤
        (p.roots.card : ℝ) * (1 / (‖z‖ - 1)) := hsum p.roots hterm
    _ = (Fintype.card V : ℝ) / (‖z‖ - 1) := by
      rw [← hsplits.natDegree_eq_card_roots,
        leeYangComplexPolynomial_natDegree]
      ring

theorem leeYangComplexFieldLogDerivative_eq_fugacity
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℂ} (hh : h.re ≠ 0) :
    leeYangComplexFieldLogDerivative G beta h =
      (beta : ℂ) * Fintype.card V -
        2 * (beta : ℂ) * Complex.exp (-2 * (beta : ℂ) * h) *
          leeYangFugacityLogDerivative G beta
            (Complex.exp (-2 * (beta : ℂ) * h)) := by
  let p : ℂ[X] := leeYangComplexPolynomial G beta
  let z : ℂ := Complex.exp (-2 * (beta : ℂ) * h)
  have hZ : leeYangComplexFieldPartition G beta h ≠ 0 :=
    leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero G hbeta hh
  have hpz : p.eval z ≠ 0 := by
    rw [show p.eval z = Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
        leeYangComplexFieldPartition G beta h by
      exact leeYangComplexFieldPartition_eq_fugacity G beta h]
    exact mul_ne_zero (Complex.exp_ne_zero _) hZ
  have hzder : HasDerivAt
      (fun w : ℂ => Complex.exp (-2 * (beta : ℂ) * w))
      (z * (-2 * (beta : ℂ))) h := by
    convert (((hasDerivAt_id h).const_mul (-2 * (beta : ℂ))).cexp)
      using 1
    all_goals simp only [id_eq, z]
    all_goals ring
  have hleft : HasDerivAt
      (fun w : ℂ => p.eval (Complex.exp (-2 * (beta : ℂ) * w)))
      (p.derivative.eval z * (z * (-2 * (beta : ℂ)))) h := by
    simpa only [Function.comp_apply] using (p.hasDerivAt z).comp h hzder
  have hpref : HasDerivAt
      (fun w : ℂ => Complex.exp (-(beta : ℂ) * w * Fintype.card V))
      (Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
        (-(beta : ℂ) * Fintype.card V)) h := by
    convert ((((hasDerivAt_id h).const_mul (-(beta : ℂ))).mul_const
      (Fintype.card V : ℂ)).cexp) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have hright : HasDerivAt
      (fun w : ℂ =>
        Complex.exp (-(beta : ℂ) * w * Fintype.card V) *
          leeYangComplexFieldPartition G beta w)
      (Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
          (-(beta : ℂ) * Fintype.card V) *
            leeYangComplexFieldPartition G beta h +
        Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
          leeYangComplexFieldMagnetizationNumerator G beta h) h := by
    exact hpref.mul (leeYangComplexFieldPartition_hasDerivAt G beta h)
  have hfun :
      (fun w : ℂ => p.eval (Complex.exp (-2 * (beta : ℂ) * w))) =
        fun w : ℂ =>
          Complex.exp (-(beta : ℂ) * w * Fintype.card V) *
            leeYangComplexFieldPartition G beta w := by
    funext w
    exact leeYangComplexFieldPartition_eq_fugacity G beta w
  have hd := congrArg (fun f : ℂ → ℂ => deriv f h) hfun
  change deriv (fun w : ℂ =>
      p.eval (Complex.exp (-2 * (beta : ℂ) * w))) h =
    deriv (fun w : ℂ =>
      Complex.exp (-(beta : ℂ) * w * Fintype.card V) *
        leeYangComplexFieldPartition G beta w) h at hd
  rw [hleft.deriv, hright.deriv] at hd
  unfold leeYangComplexFieldLogDerivative leeYangFugacityLogDerivative
  rw [leeYangComplexFieldPartition_eq_fugacity]
  field_simp [hZ]
  dsimp only [p, z] at hd
  have he1 : Complex.exp (-((beta : ℂ) * Fintype.card V * h)) =
      Complex.exp (-(beta : ℂ) * h * Fintype.card V) := by
    congr 1
    ring
  have he2 : Complex.exp (-((beta : ℂ) * 2 * h)) =
      Complex.exp (-2 * (beta : ℂ) * h) := by
    congr 1
    ring
  rw [he1, he2]
  linear_combination -hd

theorem leeYangComplexFieldLogDerivative_norm_le_rightHalfPlane
    {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : 0 < h.re) :
    ‖leeYangComplexFieldLogDerivative G beta h‖ ≤
      (Fintype.card V : ℝ) *
        (beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
          (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖)) := by
  let z : ℂ := Complex.exp (-2 * (beta : ℂ) * h)
  have hz : ‖z‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    have hre : (-2 * (beta : ℂ) * h).re = -2 * beta * h.re := by
      norm_num [Complex.mul_re]
    rw [hre]
    nlinarith
  have hfug := leeYangFugacityLogDerivative_norm_le_openUnitDisk G hbeta.le hz
  rw [leeYangComplexFieldLogDerivative_eq_fugacity G hbeta.le (ne_of_gt hh)]
  change ‖(beta : ℂ) * Fintype.card V -
      2 * (beta : ℂ) * z * leeYangFugacityLogDerivative G beta z‖ ≤ _
  calc
    ‖(beta : ℂ) * Fintype.card V -
        2 * (beta : ℂ) * z * leeYangFugacityLogDerivative G beta z‖ ≤
        ‖(beta : ℂ) * Fintype.card V‖ +
          ‖2 * (beta : ℂ) * z * leeYangFugacityLogDerivative G beta z‖ :=
      norm_sub_le _ _
    _ = beta * Fintype.card V +
        2 * beta * ‖z‖ * ‖leeYangFugacityLogDerivative G beta z‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hbeta, Complex.norm_natCast]
      norm_num
    _ ≤ beta * Fintype.card V +
        2 * beta * ‖z‖ * ((Fintype.card V : ℝ) / (1 - ‖z‖)) := by
      gcongr
    _ = (Fintype.card V : ℝ) *
        (beta + 2 * beta * ‖z‖ / (1 - ‖z‖)) := by ring

theorem leeYangComplexFieldLogDerivative_norm_le_leftHalfPlane
    {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : h.re < 0) :
    ‖leeYangComplexFieldLogDerivative G beta h‖ ≤
      (Fintype.card V : ℝ) *
        (beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
          (‖Complex.exp (-2 * (beta : ℂ) * h)‖ - 1)) := by
  let z : ℂ := Complex.exp (-2 * (beta : ℂ) * h)
  have hz : 1 < ‖z‖ := by
    rw [Complex.norm_exp, Real.one_lt_exp_iff]
    have hre : (-2 * (beta : ℂ) * h).re = -2 * beta * h.re := by
      norm_num [Complex.mul_re]
    rw [hre]
    nlinarith
  have hfug := leeYangFugacityLogDerivative_norm_le_exterior G hbeta.le hz
  rw [leeYangComplexFieldLogDerivative_eq_fugacity G hbeta.le (ne_of_lt hh)]
  change ‖(beta : ℂ) * Fintype.card V -
      2 * (beta : ℂ) * z * leeYangFugacityLogDerivative G beta z‖ ≤ _
  calc
    ‖(beta : ℂ) * Fintype.card V -
        2 * (beta : ℂ) * z * leeYangFugacityLogDerivative G beta z‖ ≤
        ‖(beta : ℂ) * Fintype.card V‖ +
          ‖2 * (beta : ℂ) * z * leeYangFugacityLogDerivative G beta z‖ :=
      norm_sub_le _ _
    _ = beta * Fintype.card V +
        2 * beta * ‖z‖ * ‖leeYangFugacityLogDerivative G beta z‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hbeta, Complex.norm_natCast]
      norm_num
    _ ≤ beta * Fintype.card V +
        2 * beta * ‖z‖ * ((Fintype.card V : ℝ) / (‖z‖ - 1)) := by
      gcongr
    _ = (Fintype.card V : ℝ) *
        (beta + 2 * beta * ‖z‖ / (‖z‖ - 1)) := by ring


noncomputable def leeYangNormalizedFieldLogDerivative
    (beta : ℝ) (h : ℂ) : ℂ :=
  leeYangComplexFieldLogDerivative G beta h / Fintype.card V

theorem leeYangNormalizedFieldLogDerivative_analyticOnNhd_re_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    AnalyticOnNhd ℂ (leeYangNormalizedFieldLogDerivative G beta)
      {h : ℂ | h.re ≠ 0} := by
  exact (leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero
    G hbeta).div_const

theorem leeYangNormalizedFieldLogDerivative_ofReal
    (beta h : ℝ) :
    leeYangNormalizedFieldLogDerivative G beta (h : ℂ) =
      (beta : ℂ) *
        (isingExpectation G beta h (fun s => ∑ v : V, spin s v) : ℂ) /
          Fintype.card V := by
  rw [leeYangNormalizedFieldLogDerivative,
    leeYangComplexFieldLogDerivative_ofReal]

theorem leeYangNormalizedFieldLogDerivative_norm_le_rightHalfPlane
    [Nonempty V] {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : 0 < h.re) :
    ‖leeYangNormalizedFieldLogDerivative G beta h‖ ≤
      beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
        (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖) := by
  have hraw := leeYangComplexFieldLogDerivative_norm_le_rightHalfPlane G hbeta hh
  unfold leeYangNormalizedFieldLogDerivative
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
    (0 : ℝ) < Fintype.card V)).2
  simpa only [mul_comm] using hraw

theorem leeYangNormalizedFieldLogDerivative_norm_le_leftHalfPlane
    [Nonempty V] {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : h.re < 0) :
    ‖leeYangNormalizedFieldLogDerivative G beta h‖ ≤
      beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ /
        (‖Complex.exp (-2 * (beta : ℂ) * h)‖ - 1) := by
  have hraw := leeYangComplexFieldLogDerivative_norm_le_leftHalfPlane G hbeta hh
  unfold leeYangNormalizedFieldLogDerivative
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
    (0 : ℝ) < Fintype.card V)).2
  simpa only [mul_comm] using hraw

end StatMech.FrontierA
