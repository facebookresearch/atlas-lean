/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.PSeries

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import MathlibExt.Analysis.Calculus.EulerMaclaurinFormula
import MathlibExt.Analysis.SpecialFunctions.ExpSubOneMittagLeffler

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 14

This file proves explicit finite asymptotic expansions, with error bounds, for the
Lambert series with summands `1 / (exp (j * x) - 1)` and `1 / (exp (j * x) + 1)`.

The namespaces `Entry10Centralbinomialexpansion` / `Entry10Centralbinomialfull` and the
two theorem names `ramanujan_part1_ch6_entry10_centralbinomialexpansion` /
`ramanujan_part1_ch6_entry10_centralbinomialfull` are frozen Wanted identifiers and are
kept unchanged.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry10Centralbinomialexpansion

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter6Entry14PlusCorrection (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range n,
    let k := j + 1
    (((2 : ℝ) ^ (2 * k) - 1) * (bernoulli (2 * k) : ℝ) ^ 2 *
      x ^ (2 * k - 1)) /
      (((2 * k : ℕ) : ℝ) * ((2 * k).factorial : ℝ))

def chapter6Entry14PlusTerm (x : ℝ) (j : ℕ) : ℝ :=
  1 / (Real.exp ((j + 1 : ℕ) * x) + 1)

def chapter6Entry14PlusSum (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter6Entry14PlusTerm x j

end

end Entry10Centralbinomialexpansion

namespace Entry10Centralbinomialfull

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter6Entry14MinusCorrection (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range n,
    let k := j + 1
    ((bernoulli (2 * k) : ℝ) ^ 2 * x ^ (2 * k - 1)) /
      (((2 * k : ℕ) : ℝ) * ((2 * k).factorial : ℝ))

def chapter6Entry14MinusTerm (x : ℝ) (j : ℕ) : ℝ :=
  1 / (Real.exp ((j + 1 : ℕ) * x) - 1)

def chapter6Entry14MinusSum (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter6Entry14MinusTerm x j

private lemma ch6Entry14_minusTerm_summable (x : ℝ) (hx : 0 < x) :
    Summable (chapter6Entry14MinusTerm x) := by
  let E := Real.exp x
  have hE : 1 < E := Real.one_lt_exp_iff.mpr hx
  have hEinv : ‖E⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (lt_trans zero_lt_one hE))]
    exact inv_lt_one_of_one_lt₀ hE
  apply Summable.of_norm_bounded
      ((summable_geometric_of_norm_lt_one hEinv).mul_left (1 / (E - 1)))
  intro j
  have hpow : 1 ≤ E ^ j := one_le_pow₀ hE.le
  have hdenpos : 0 < E ^ (j + 1) - 1 := by
    rw [pow_succ]
    nlinarith [pow_pos (lt_trans zero_lt_one hE) j]
  have hminorpos : 0 < (E - 1) * E ^ j :=
    mul_pos (sub_pos.mpr hE) (pow_pos (lt_trans zero_lt_one hE) j)
  have hden : (E - 1) * E ^ j ≤ E ^ (j + 1) - 1 := by
    rw [pow_succ]
    nlinarith
  rw [chapter6Entry14MinusTerm, Real.exp_nat_mul, show Real.exp x = E from rfl]
  rw [Real.norm_of_nonneg (one_div_nonneg.mpr hdenpos.le)]
  calc
    1 / (E ^ (j + 1) - 1) ≤ 1 / ((E - 1) * E ^ j) :=
      one_div_le_one_div_of_le hminorpos hden
    _ = 1 / (E - 1) * E⁻¹ ^ j := by
      rw [inv_pow]
      field_simp

private def ch6Entry14_aterm (m : ℕ) : ℝ := 2 * Real.pi * (m + 1)

private def ch6Entry14_rterm (m : ℕ) (u : ℝ) : ℝ :=
  2 * u / (u ^ 2 + ch6Entry14_aterm m ^ 2)

private def ch6Entry14_cterm (m : ℕ) (z : ℂ) : ℂ :=
  1 / (z - Complex.I * ch6Entry14_aterm m) + 1 / (z + Complex.I * ch6Entry14_aterm m)

private lemma ch6Entry14_apos (m : ℕ) : 0 < ch6Entry14_aterm m := by
  unfold ch6Entry14_aterm
  positivity

private lemma ch6Entry14_cterm_real (m : ℕ) (u : ℝ) :
    ch6Entry14_rterm m u = (ch6Entry14_cterm m (u : ℂ)).re := by
  have ha : (ch6Entry14_aterm m : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (ch6Entry14_apos m))
  have hminus : (u : ℂ) - Complex.I * ch6Entry14_aterm m ≠ 0 := by
    intro h
    have him := congr_arg Complex.im h
    simp only [sub_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re,
      one_mul, zero_add, zero_sub, zero_im, neg_eq_zero] at him
    exact (ne_of_gt (ch6Entry14_apos m)) him
  have hplus : (u : ℂ) + Complex.I * ch6Entry14_aterm m ≠ 0 := by
    intro h
    have him := congr_arg Complex.im h
    simp only [add_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re,
      one_mul, zero_add, zero_im] at him
    exact (ne_of_gt (ch6Entry14_apos m)) him
  have hden : (u : ℂ) ^ 2 + (ch6Entry14_aterm m : ℂ) ^ 2 ≠ 0 := by
    have heq : (u : ℂ) ^ 2 + (ch6Entry14_aterm m : ℂ) ^ 2 =
        ((u ^ 2 + ch6Entry14_aterm m ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [heq]
    apply Complex.ofReal_ne_zero.mpr
    nlinarith [sq_pos_of_pos (ch6Entry14_apos m)]
  rw [ch6Entry14_rterm, ch6Entry14_cterm]
  have hc :
      (1 / ((u : ℂ) - Complex.I * ch6Entry14_aterm m) +
          1 / ((u : ℂ) + Complex.I * ch6Entry14_aterm m)) =
        ((2 * u / (u ^ 2 + ch6Entry14_aterm m ^ 2) : ℝ) : ℂ) := by
    push_cast
    field_simp [hminus, hplus, hden]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hr := congr_arg Complex.re hc
  calc
    2 * u / (u ^ 2 + ch6Entry14_aterm m ^ 2) =
        (((2 * u / (u ^ 2 + ch6Entry14_aterm m ^ 2) : ℝ) : ℂ)).re :=
      (Complex.ofReal_re _).symm
    _ = _ := hr.symm

private def ch6Entry14_ctermDeriv (m k : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * k ! *
    ((z - Complex.I * ch6Entry14_aterm m) ^ (-1 - k : ℤ) +
      (z + Complex.I * ch6Entry14_aterm m) ^ (-1 - k : ℤ))

private lemma ch6Entry14_cderiv_zero_real (m : ℕ) (u : ℝ) :
    ch6Entry14_rterm m u = (ch6Entry14_ctermDeriv m 0 (u : ℂ)).re := by
  rw [ch6Entry14_cterm_real m u]
  unfold ch6Entry14_ctermDeriv ch6Entry14_cterm
  simp [zpow_neg]

private lemma ch6Entry14_hasDerivAt_cderiv (m k : ℕ) (u : ℝ) :
    HasDerivAt (ch6Entry14_ctermDeriv m k) (ch6Entry14_ctermDeriv m (k + 1) (u : ℂ)) (u : ℂ) := by
  have hminus : (u : ℂ) - Complex.I * ch6Entry14_aterm m ≠ 0 := by
    intro h
    have him := congr_arg Complex.im h
    simp only [sub_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re,
      one_mul, zero_add, zero_sub, zero_im, neg_eq_zero] at him
    exact (ne_of_gt (ch6Entry14_apos m)) him
  have hplus : (u : ℂ) + Complex.I * ch6Entry14_aterm m ≠ 0 := by
    intro h
    have him := congr_arg Complex.im h
    simp only [add_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re,
      one_mul, zero_add, zero_im] at him
    exact (ne_of_gt (ch6Entry14_apos m)) him
  have hdm := (hasDerivAt_zpow (-1 - k : ℤ)
      ((u : ℂ) - Complex.I * ch6Entry14_aterm m) (Or.inl hminus)).comp (u : ℂ)
        ((hasDerivAt_id (u : ℂ)).sub_const (Complex.I * ch6Entry14_aterm m))
  have hdp := (hasDerivAt_zpow (-1 - k : ℤ)
      ((u : ℂ) + Complex.I * ch6Entry14_aterm m) (Or.inl hplus)).comp (u : ℂ)
        ((hasDerivAt_id (u : ℂ)).add_const (Complex.I * ch6Entry14_aterm m))
  unfold ch6Entry14_ctermDeriv
  convert (hdm.add hdp).const_mul ((-1 : ℂ) ^ k * k !) using 1
  · norm_num
  · push_cast
    have he : (-1 - (k : ℤ)) - 1 = -1 - ((k + 1 : ℕ) : ℤ) := by omega
    rw [he]
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    ring

private def ch6Entry14_dterm (q : ℕ) (u : ℝ) (m : ℕ) : ℝ :=
  (ch6Entry14_ctermDeriv m q (u : ℂ)).re

private lemma ch6Entry14_hasDerivAt_dterm (q m : ℕ) (u : ℝ) :
    HasDerivAt (fun y => ch6Entry14_dterm q y m) (ch6Entry14_dterm (q + 1) u m) u := by
  exact (ch6Entry14_hasDerivAt_cderiv m q u).real_of_complex

private lemma ch6Entry14_rterm_eq_dterm_zero (m : ℕ) :
    ch6Entry14_rterm m = fun u => ch6Entry14_dterm 0 u m := by
  funext u
  exact ch6Entry14_cderiv_zero_real m u

private def ch6Entry14_derivBound (q m : ℕ) : ℝ :=
  2 * q.factorial / ch6Entry14_aterm m ^ (q + 1)

private lemma ch6Entry14_norm_sub_I_mul_le (m : ℕ) (u : ℝ) :
    ch6Entry14_aterm m ≤ ‖(u : ℂ) - Complex.I * ch6Entry14_aterm m‖ := by
  have h := Complex.abs_im_le_norm ((u : ℂ) - Complex.I * ch6Entry14_aterm m)
  simpa [abs_of_pos (ch6Entry14_apos m)] using h

private lemma ch6Entry14_norm_add_I_mul_le (m : ℕ) (u : ℝ) :
    ch6Entry14_aterm m ≤ ‖(u : ℂ) + Complex.I * ch6Entry14_aterm m‖ := by
  have h := Complex.abs_im_le_norm ((u : ℂ) + Complex.I * ch6Entry14_aterm m)
  simpa [abs_of_pos (ch6Entry14_apos m)] using h

private lemma ch6Entry14_norm_zpow_sub_le (m q : ℕ) (u : ℝ) :
    ‖((u : ℂ) - Complex.I * ch6Entry14_aterm m) ^ (-1 - q : ℤ)‖ ≤
      1 / ch6Entry14_aterm m ^ (q + 1) := by
  rw [norm_zpow]
  have he : (-1 - (q : ℤ)) = -((q + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  have hp := pow_le_pow_left₀ (le_of_lt (ch6Entry14_apos m))
    (ch6Entry14_norm_sub_I_mul_le m u) (q + 1)
  simpa only [one_div] using
    (one_div_le_one_div_of_le (pow_pos (ch6Entry14_apos m) (q + 1)) hp)

private lemma ch6Entry14_norm_zpow_add_le (m q : ℕ) (u : ℝ) :
    ‖((u : ℂ) + Complex.I * ch6Entry14_aterm m) ^ (-1 - q : ℤ)‖ ≤
      1 / ch6Entry14_aterm m ^ (q + 1) := by
  rw [norm_zpow]
  have he : (-1 - (q : ℤ)) = -((q + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  have hp := pow_le_pow_left₀ (le_of_lt (ch6Entry14_apos m))
    (ch6Entry14_norm_add_I_mul_le m u) (q + 1)
  simpa only [one_div] using
    (one_div_le_one_div_of_le (pow_pos (ch6Entry14_apos m) (q + 1)) hp)

private lemma ch6Entry14_norm_dterm_le (q m : ℕ) (u : ℝ) :
    ‖ch6Entry14_dterm q u m‖ ≤ ch6Entry14_derivBound q m := by
  rw [Real.norm_eq_abs]
  calc
    |ch6Entry14_dterm q u m| ≤ ‖ch6Entry14_ctermDeriv m q (u : ℂ)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ (q.factorial : ℝ) *
        (‖((u : ℂ) - Complex.I * ch6Entry14_aterm m) ^ (-1 - q : ℤ)‖ +
          ‖((u : ℂ) + Complex.I * ch6Entry14_aterm m) ^ (-1 - q : ℤ)‖) := by
      unfold ch6Entry14_ctermDeriv
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        Complex.norm_natCast, one_mul]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Nat.cast_nonneg _)
    _ ≤ (q.factorial : ℝ) *
        (1 / ch6Entry14_aterm m ^ (q + 1) + 1 / ch6Entry14_aterm m ^ (q + 1)) := by
      gcongr
      · exact ch6Entry14_norm_zpow_sub_le m q u
      · exact ch6Entry14_norm_zpow_add_le m q u
    _ = ch6Entry14_derivBound q m := by
      unfold ch6Entry14_derivBound
      ring

private lemma ch6Entry14_summable_derivBound (q : ℕ) (hq : 1 ≤ q) :
    Summable (ch6Entry14_derivBound q) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ (q + 1))⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by omega)
  have hshift : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ (q + 1))⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have hmul := hshift.mul_left
    (2 * (q.factorial : ℝ) / (2 * Real.pi) ^ (q + 1))
  apply hmul.congr
  intro m
  unfold ch6Entry14_derivBound ch6Entry14_aterm
  change 2 * (q.factorial : ℝ) / (2 * Real.pi) ^ (q + 1) *
      (((m + 1 : ℕ) : ℝ) ^ (q + 1))⁻¹ =
    2 * (q.factorial : ℝ) /
      ((2 * Real.pi) * ((m : ℝ) + 1)) ^ (q + 1)
  conv_rhs => rw [mul_pow]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

private lemma ch6Entry14_summable_dterm_zero (q : ℕ) :
    Summable (fun m => ch6Entry14_dterm q 0 m) := by
  cases q with
  | zero =>
      apply summable_zero.congr
      intro m
      calc
        0 = ch6Entry14_rterm m 0 := by simp [ch6Entry14_rterm]
        _ = ch6Entry14_dterm 0 0 m := ch6Entry14_cderiv_zero_real m 0
  | succ q =>
      apply Summable.of_norm_bounded (ch6Entry14_summable_derivBound (q + 1) (by omega))
      intro m
      exact ch6Entry14_norm_dterm_le (q + 1) m 0

private lemma ch6Entry14_hasDerivAt_tsum_dterm (q : ℕ) (u : ℝ) :
    HasDerivAt (fun y => ∑' m : ℕ, ch6Entry14_dterm q y m)
      (∑' m : ℕ, ch6Entry14_dterm (q + 1) u m) u := by
  exact hasDerivAt_tsum_of_isPreconnected (ch6Entry14_summable_derivBound (q + 1) (by omega))
    isOpen_univ isPreconnected_univ
    (fun m y _ => ch6Entry14_hasDerivAt_dterm q m y)
    (fun m y _ => ch6Entry14_norm_dterm_le (q + 1) m y)
    (Set.mem_univ 0) (ch6Entry14_summable_dterm_zero q) (Set.mem_univ u)

private lemma ch6Entry14_differentiable_tsum_dterm (q : ℕ) :
    Differentiable ℝ (fun y => ∑' m : ℕ, ch6Entry14_dterm q y m) :=
  fun u => (ch6Entry14_hasDerivAt_tsum_dterm q u).differentiableAt

private def ch6Entry14_kernelCore (u : ℝ) : ℝ :=
  ∑' m : ℕ, ch6Entry14_rterm m u

private lemma ch6Entry14_iteratedDeriv_kernelCore (q : ℕ) (u : ℝ) :
    iteratedDeriv q ch6Entry14_kernelCore u = ∑' m : ℕ, ch6Entry14_dterm q u m := by
  induction q generalizing u with
  | zero =>
      rw [iteratedDeriv_zero]
      unfold ch6Entry14_kernelCore
      apply tsum_congr
      intro m
      exact congrFun (ch6Entry14_rterm_eq_dterm_zero m) u
  | succ q ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv q ch6Entry14_kernelCore =
          fun y => ∑' m : ℕ, ch6Entry14_dterm q y m := by
        funext y
        exact ih y
      rw [hfun]
      exact (ch6Entry14_hasDerivAt_tsum_dterm q u).deriv

private lemma ch6Entry14_contDiff_kernelCore : ContDiff ℝ ∞ ch6Entry14_kernelCore := by
  rw [contDiff_iff_iteratedDeriv]
  constructor
  · intro q _
    rw [show iteratedDeriv q ch6Entry14_kernelCore = fun y => ∑' m : ℕ, ch6Entry14_dterm q y m by
      funext y
      exact ch6Entry14_iteratedDeriv_kernelCore q y]
    exact (ch6Entry14_differentiable_tsum_dterm q).continuous
  · intro q _
    rw [show iteratedDeriv q ch6Entry14_kernelCore = fun y => ∑' m : ℕ, ch6Entry14_dterm q y m by
      funext y
      exact ch6Entry14_iteratedDeriv_kernelCore q y]
    exact ch6Entry14_differentiable_tsum_dterm q

private def ch6Entry14_kernel (u : ℝ) : ℝ :=
  -1 / 2 + ch6Entry14_kernelCore u

private lemma ch6Entry14_contDiff_kernel : ContDiff ℝ ∞ ch6Entry14_kernel := by
  exact contDiff_const.add ch6Entry14_contDiff_kernelCore

private lemma ch6Entry14_kernel_zero : ch6Entry14_kernel 0 = -1 / 2 := by
  unfold ch6Entry14_kernel ch6Entry14_kernelCore
  have hz : (fun m : ℕ => ch6Entry14_rterm m 0) = 0 := by
    funext m
    simp [ch6Entry14_rterm]
  rw [hz]
  change -1 / 2 + (∑' _m : ℕ, (0 : ℝ)) = -1 / 2
  rw [tsum_zero, add_zero]

private lemma ch6Entry14_rterm_eq_partialFractionTerm (m : ℕ) (u : ℝ) :
    ch6Entry14_rterm m u = 2 * u / (u ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2) := by
  unfold ch6Entry14_rterm ch6Entry14_aterm
  congr 1
  push_cast
  ring

private lemma ch6Entry14_kernel_eq (u : ℝ) (hu : u ≠ 0) :
    ch6Entry14_kernel u = 1 / (Real.exp u - 1) - 1 / u := by
  have h := MetaMathlibExt.one_div_exp_sub_one_eq_tsum u hu
  have hsum : ch6Entry14_kernelCore u =
      ∑' m : ℕ, 2 * u / (u ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2) := by
    unfold ch6Entry14_kernelCore
    exact tsum_congr fun m => ch6Entry14_rterm_eq_partialFractionTerm m u
  unfold ch6Entry14_kernel
  rw [hsum]
  linarith

private lemma ch6Entry14_zpow_I_mul_even (a : ℝ) (ha : a ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    (Complex.I * (a : ℂ)) ^ (-1 - ((2 * k - 1 : ℕ) : ℤ)) =
      (((-1 : ℝ) ^ k / a ^ (2 * k) : ℝ) : ℂ) := by
  have he : (-1 - ((2 * k - 1 : ℕ) : ℤ)) = -((2 * k : ℕ) : ℤ) := by omega
  rw [he, zpow_neg_coe_of_pos _ (by omega)]
  have hpow : (Complex.I * (a : ℂ)) ^ (2 * k) =
      (((-1 : ℝ) ^ k * a ^ (2 * k) : ℝ) : ℂ) := by
    rw [pow_mul]
    have hsq : (Complex.I * (a : ℂ)) ^ 2 = ((-a ^ 2 : ℝ) : ℂ) := by
      rw [pow_two]
      calc
        Complex.I * (a : ℂ) * (Complex.I * (a : ℂ)) =
            (Complex.I * Complex.I) * ((a : ℂ) * (a : ℂ)) := by ring
        _ = ((-a ^ 2 : ℝ) : ℂ) := by rw [Complex.I_mul_I]; push_cast; ring
    rw [hsq]
    norm_cast
    rw [show -a ^ 2 = (-1 : ℝ) * a ^ 2 by ring, mul_pow, ← pow_mul]
    norm_num
  rw [hpow]
  norm_cast
  have hap : a ^ (2 * k) ≠ 0 := pow_ne_zero _ ha
  field_simp [hap]
  norm_cast
  rw [← pow_mul]
  simp

private lemma ch6Entry14_zpow_neg_I_mul_even (a : ℝ) (ha : a ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    (-Complex.I * (a : ℂ)) ^ (-1 - ((2 * k - 1 : ℕ) : ℤ)) =
      (((-1 : ℝ) ^ k / a ^ (2 * k) : ℝ) : ℂ) := by
  have he : (-1 - ((2 * k - 1 : ℕ) : ℤ)) = -((2 * k : ℕ) : ℤ) := by omega
  rw [he, zpow_neg_coe_of_pos _ (by omega)]
  have hpow : (-Complex.I * (a : ℂ)) ^ (2 * k) =
      (((-1 : ℝ) ^ k * a ^ (2 * k) : ℝ) : ℂ) := by
    rw [pow_mul]
    have hsq : (-Complex.I * (a : ℂ)) ^ 2 = ((-a ^ 2 : ℝ) : ℂ) := by
      rw [pow_two]
      calc
        -Complex.I * (a : ℂ) * (-Complex.I * (a : ℂ)) =
            (Complex.I * Complex.I) * ((a : ℂ) * (a : ℂ)) := by ring
        _ = ((-a ^ 2 : ℝ) : ℂ) := by rw [Complex.I_mul_I]; push_cast; ring
    rw [hsq]
    norm_cast
    rw [show -a ^ 2 = (-1 : ℝ) * a ^ 2 by ring, mul_pow, ← pow_mul]
    norm_num
  rw [hpow]
  norm_cast
  have hap : a ^ (2 * k) ≠ 0 := pow_ne_zero _ ha
  field_simp [hap]
  norm_cast
  rw [← pow_mul]
  simp

private lemma ch6Entry14_dterm_odd_zero (m k : ℕ) (hk : 1 ≤ k) :
    ch6Entry14_dterm (2 * k - 1) 0 m =
      2 * ((2 * k - 1).factorial : ℝ) * (-1 : ℝ) ^ (k - 1) /
        ch6Entry14_aterm m ^ (2 * k) := by
  unfold ch6Entry14_dterm
  have ha : ch6Entry14_aterm m ≠ 0 := ne_of_gt (ch6Entry14_apos m)
  have hc : ch6Entry14_ctermDeriv m (2 * k - 1) 0 =
      ((2 * ((2 * k - 1).factorial : ℝ) * (-1 : ℝ) ^ (k - 1) /
        ch6Entry14_aterm m ^ (2 * k) : ℝ) : ℂ) := by
    unfold ch6Entry14_ctermDeriv
    simp only [zero_sub, zero_add]
    have hneg : -(Complex.I * (ch6Entry14_aterm m : ℂ)) =
        -Complex.I * (ch6Entry14_aterm m : ℂ) := by ring
    rw [hneg]
    rw [ch6Entry14_zpow_neg_I_mul_even (ch6Entry14_aterm m) ha k hk,
      ch6Entry14_zpow_I_mul_even (ch6Entry14_aterm m) ha k hk]
    norm_cast
    have hq : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
    rw [hq, pow_succ, pow_mul]
    norm_num
    have hk' : k - 1 + 1 = k := by omega
    have hsign : -(-1 : ℝ) ^ k = (-1 : ℝ) ^ (k - 1) := by
      have hp : (-1 : ℝ) ^ k = (-1 : ℝ) ^ (k - 1 + 1) :=
        congr_arg (fun t : ℕ => (-1 : ℝ) ^ t) hk'.symm
      rw [hp, pow_succ]
      ring
    rw [← hsign]
    ring
  have hr := congr_arg Complex.re hc
  calc
    (ch6Entry14_ctermDeriv m (2 * k - 1) 0).re =
        (((2 * ((2 * k - 1).factorial : ℝ) * (-1 : ℝ) ^ (k - 1) /
          ch6Entry14_aterm m ^ (2 * k) : ℝ) : ℂ)).re := hr
    _ = _ := Complex.ofReal_re _

private lemma ch6Entry14_tsum_one_div_succ_pow (k : ℕ) (hk : 1 ≤ k) :
    (∑' m : ℕ, 1 / (((m + 1 : ℕ) : ℝ) ^ (2 * k))) =
      (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) *
        (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) := by
  have hz := hasSum_zeta_nat (Nat.ne_of_gt hk)
  have hs := hz.summable
  have hdecomp := hs.sum_add_tsum_nat_add 1
  rw [hz.tsum_eq] at hdecomp
  have hk2 : 2 * k ≠ 0 := by omega
  simp [zero_pow hk2] at hdecomp
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using hdecomp

private lemma ch6Entry14_tsum_dterm_odd_zero (k : ℕ) (hk : 1 ≤ k) :
    (∑' m : ℕ, ch6Entry14_dterm (2 * k - 1) 0 m) = (bernoulli (2 * k) : ℝ) / (2 * k) := by
  let C : ℝ := 2 * ((2 * k - 1).factorial : ℝ) * (-1 : ℝ) ^ (k - 1) /
    (2 * Real.pi) ^ (2 * k)
  have hterm : ∀ m : ℕ, ch6Entry14_dterm (2 * k - 1) 0 m =
      C * (1 / (((m + 1 : ℕ) : ℝ) ^ (2 * k))) := by
    intro m
    rw [ch6Entry14_dterm_odd_zero m k hk]
    unfold C ch6Entry14_aterm
    push_cast
    change 2 * ((2 * k - 1).factorial : ℝ) * (-1 : ℝ) ^ (k - 1) /
        ((2 * Real.pi) * ((m : ℝ) + 1)) ^ (2 * k) =
      (2 * ((2 * k - 1).factorial : ℝ) * (-1 : ℝ) ^ (k - 1) /
        (2 * Real.pi) ^ (2 * k)) *
        (1 / (((m : ℝ) + 1) ^ (2 * k)))
    conv_lhs => rw [mul_pow]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [tsum_congr hterm, tsum_mul_left, ch6Entry14_tsum_one_div_succ_pow k hk]
  unfold C
  have hsign : (-1 : ℝ) ^ (k - 1) * (-1 : ℝ) ^ (k + 1) = 1 := by
    rw [← pow_add]
    have he : k - 1 + (k + 1) = 2 * k := by omega
    rw [he, pow_mul]
    norm_num
  have hfac : ((2 * k).factorial : ℝ) =
      (2 * k : ℝ) * ((2 * k - 1).factorial : ℝ) := by
    have he : 2 * k = (2 * k - 1) + 1 := by omega
    have hfacNat : (2 * k).factorial =
        (2 * k) * (2 * k - 1).factorial := by
      conv_lhs => rw [he, Nat.factorial_succ]
      congr 1
      omega
    exact_mod_cast hfacNat
  have hkR : (2 * k : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hfac]
  field_simp [hkR, hpi]
  rw [mul_pow]
  rw [show (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) by
    have he : 2 * k = (2 * k - 1) + 1 := by omega
    have hp : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ ((2 * k - 1) + 1) :=
      congr_arg (fun t : ℕ => (2 : ℝ) ^ t) he
    rw [hp, pow_succ]
    ring]
  rw [mul_assoc (2 : ℝ) ((-1 : ℝ) ^ (k - 1)) ((-1 : ℝ) ^ (k + 1)), hsign]
  ring

private lemma ch6Entry14_iteratedDeriv_kernel_odd_zero (k : ℕ) (hk : 1 ≤ k) :
    iteratedDeriv (2 * k - 1) ch6Entry14_kernel 0 = (bernoulli (2 * k) : ℝ) / (2 * k) := by
  change iteratedDeriv (2 * k - 1) (fun u => -1 / 2 + ch6Entry14_kernelCore u) 0 = _
  rw [iteratedDeriv_const_add (by omega) (-1 / 2)]
  rw [ch6Entry14_iteratedDeriv_kernelCore, ch6Entry14_tsum_dterm_odd_zero k hk]

private lemma ch6Entry14_norm_zpow_sub_odd (m n : ℕ) (u : ℝ) :
    ‖((u : ℂ) - Complex.I * ch6Entry14_aterm m) ^ (-1 - (2 * n + 1 : ℕ) : ℤ)‖ =
      1 / (u ^ 2 + ch6Entry14_aterm m ^ 2) ^ (n + 1) := by
  rw [norm_zpow]
  have he : (-1 - ((2 * n + 1 : ℕ) : ℤ)) = -((2 * (n + 1) : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  rw [one_div]
  congr 1
  rw [pow_mul, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

private lemma ch6Entry14_norm_zpow_add_odd (m n : ℕ) (u : ℝ) :
    ‖((u : ℂ) + Complex.I * ch6Entry14_aterm m) ^ (-1 - (2 * n + 1 : ℕ) : ℤ)‖ =
      1 / (u ^ 2 + ch6Entry14_aterm m ^ 2) ^ (n + 1) := by
  rw [norm_zpow]
  have he : (-1 - ((2 * n + 1 : ℕ) : ℤ)) = -((2 * (n + 1) : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  rw [one_div]
  congr 1
  rw [pow_mul, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

private lemma ch6Entry14_norm_dterm_odd_le (m n : ℕ) (u : ℝ) :
    ‖ch6Entry14_dterm (2 * n + 1) u m‖ ≤
      2 * ((2 * n + 1).factorial : ℝ) /
        (u ^ 2 + ch6Entry14_aterm m ^ 2) ^ (n + 1) := by
  rw [Real.norm_eq_abs]
  calc
    |ch6Entry14_dterm (2 * n + 1) u m| ≤ ‖ch6Entry14_ctermDeriv m (2 * n + 1) (u : ℂ)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ((2 * n + 1).factorial : ℝ) *
        (‖((u : ℂ) - Complex.I * ch6Entry14_aterm m) ^ (-1 - (2 * n + 1 : ℕ) : ℤ)‖ +
          ‖((u : ℂ) + Complex.I * ch6Entry14_aterm m) ^ (-1 - (2 * n + 1 : ℕ) : ℤ)‖) := by
      unfold ch6Entry14_ctermDeriv
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        Complex.norm_natCast, one_mul]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Nat.cast_nonneg _)
    _ = _ := by
      rw [ch6Entry14_norm_zpow_sub_odd, ch6Entry14_norm_zpow_add_odd]
      ring

private lemma ch6Entry14_norm_dterm_odd_le_quadratic (m n : ℕ) (u : ℝ) :
    ‖ch6Entry14_dterm (2 * n + 1) u m‖ ≤
      (2 * ((2 * n + 1).factorial : ℝ) / ch6Entry14_aterm m ^ (2 * n)) *
        (1 / (u ^ 2 + ch6Entry14_aterm m ^ 2)) := by
  have ha : 0 < ch6Entry14_aterm m := ch6Entry14_apos m
  have hb : 0 < u ^ 2 + ch6Entry14_aterm m ^ 2 := by positivity
  have hab : ch6Entry14_aterm m ^ 2 ≤ u ^ 2 + ch6Entry14_aterm m ^ 2 := by
    nlinarith [sq_nonneg u]
  have haPow : ch6Entry14_aterm m ^ (2 * n) =
      (ch6Entry14_aterm m ^ 2) ^ n := by
    rw [pow_mul]
  have hpow : ch6Entry14_aterm m ^ (2 * n) * (u ^ 2 + ch6Entry14_aterm m ^ 2) ≤
      (u ^ 2 + ch6Entry14_aterm m ^ 2) ^ (n + 1) := by
    rw [pow_succ, haPow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (sq_nonneg (ch6Entry14_aterm m)) hab n) hb.le
  calc
    ‖ch6Entry14_dterm (2 * n + 1) u m‖ ≤
        2 * ((2 * n + 1).factorial : ℝ) /
          (u ^ 2 + ch6Entry14_aterm m ^ 2) ^ (n + 1) := ch6Entry14_norm_dterm_odd_le m n u
    _ ≤ 2 * ((2 * n + 1).factorial : ℝ) /
        (ch6Entry14_aterm m ^ (2 * n) * (u ^ 2 + ch6Entry14_aterm m ^ 2)) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos (pow_pos ha _) hb) hpow
    _ = _ := by
      field_simp

private lemma ch6Entry14_integral_inv_sq_add_sq_le (a L : ℝ) (ha : 0 < a) :
    ∫ u in (0 : ℝ)..L, 1 / (u ^ 2 + a ^ 2) ≤ Real.pi / (2 * a) := by
  rw [show (∫ u in (0 : ℝ)..L, 1 / (u ^ 2 + a ^ 2)) =
      a⁻¹ * (Real.arctan (L / a) - Real.arctan (0 / a)) by
    simpa only [add_comm, one_div] using
      (integral_inv_sq_add_sq (a := 0) (b := L) (c := a) ha.ne')]
  simp only [zero_div, Real.arctan_zero, sub_zero]
  have hatan : Real.arctan (L / a) ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two _).le
  calc
    a⁻¹ * Real.arctan (L / a) ≤ a⁻¹ * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left hatan (by positivity)
    _ = Real.pi / (2 * a) := by ring

private lemma ch6Entry14_continuous_dterm (q m : ℕ) : Continuous (ch6Entry14_dterm q · m) :=
  continuous_iff_continuousAt.mpr fun u ↦ (ch6Entry14_hasDerivAt_dterm q m u).continuousAt

private lemma ch6Entry14_integral_norm_dterm_odd_le (m n : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∫ u in (0 : ℝ)..L, ‖ch6Entry14_dterm (2 * n + 1) u m‖ ≤
      Real.pi * ((2 * n + 1).factorial : ℝ) / ch6Entry14_aterm m ^ (2 * n + 1) := by
  let C : ℝ := 2 * ((2 * n + 1).factorial : ℝ) / ch6Entry14_aterm m ^ (2 * n)
  have ha : 0 < ch6Entry14_aterm m := ch6Entry14_apos m
  have hrat : Continuous (fun u : ℝ ↦ 1 / (u ^ 2 + ch6Entry14_aterm m ^ 2)) := by
    exact continuous_const.div
      (continuous_id.pow 2 |>.add continuous_const) fun u ↦ by positivity
  have hmono :
      (∫ u in (0 : ℝ)..L, ‖ch6Entry14_dterm (2 * n + 1) u m‖) ≤
        ∫ u in (0 : ℝ)..L, C * (1 / (u ^ 2 + ch6Entry14_aterm m ^ 2)) := by
    apply intervalIntegral.integral_mono_on hL
      ((ch6Entry14_continuous_dterm (2 * n + 1) m).norm.intervalIntegrable 0 L)
      ((continuous_const.mul hrat).intervalIntegrable 0 L)
    intro u _
    exact ch6Entry14_norm_dterm_odd_le_quadratic m n u
  rw [intervalIntegral.integral_const_mul] at hmono
  calc
    (∫ u in (0 : ℝ)..L, ‖ch6Entry14_dterm (2 * n + 1) u m‖) ≤
        C * ∫ u in (0 : ℝ)..L, 1 / (u ^ 2 + ch6Entry14_aterm m ^ 2) := hmono
    _ ≤ C * (Real.pi / (2 * ch6Entry14_aterm m)) :=
      mul_le_mul_of_nonneg_left (ch6Entry14_integral_inv_sq_add_sq_le _ _ ha) (by
        unfold C
        positivity)
    _ = Real.pi * ((2 * n + 1).factorial : ℝ) /
        ch6Entry14_aterm m ^ (2 * n + 1) := by
      unfold C
      rw [pow_succ]
      field_simp

private lemma ch6Entry14_summable_dterm (q : ℕ) (hq : 1 ≤ q) (u : ℝ) :
    Summable (ch6Entry14_dterm q u) :=
  (ch6Entry14_summable_derivBound q hq).of_norm_bounded fun m ↦
    ch6Entry14_norm_dterm_le q m u

private lemma ch6Entry14_summable_odd_integralBound (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun m : ℕ ↦
      Real.pi * ((2 * n + 1).factorial : ℝ) / ch6Entry14_aterm m ^ (2 * n + 1)) := by
  have hp : 1 < 2 * n + 1 := by omega
  have hs : Summable (fun m : ℕ ↦
      1 / (((m + 1 : ℕ) : ℝ) ^ (2 * n + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr hp)
  let C : ℝ := Real.pi * ((2 * n + 1).factorial : ℝ) /
    (2 * Real.pi) ^ (2 * n + 1)
  convert hs.mul_left C using 1
  ext m
  unfold C ch6Entry14_aterm
  push_cast
  rw [mul_pow]
  field_simp

private lemma ch6Entry14_integral_norm_iteratedDeriv_kernel_odd_le (n : ℕ) (L : ℝ)
    (hn : 1 ≤ n) (hL : 0 ≤ L) :
    ∫ u in (0 : ℝ)..L, ‖iteratedDeriv (2 * n + 1) ch6Entry14_kernel u‖ ≤
      ∑' m : ℕ,
        Real.pi * ((2 * n + 1).factorial : ℝ) / ch6Entry14_aterm m ^ (2 * n + 1) := by
  let f : ℕ → C(ℝ, ℝ) := fun m ↦
    ⟨fun u ↦ ‖ch6Entry14_dterm (2 * n + 1) u m‖, (ch6Entry14_continuous_dterm (2 * n + 1) m).norm⟩
  have hsup : Summable (fun m : ℕ ↦
      ‖(f m).restrict
        (⟨Set.uIcc 0 L, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
    apply (ch6Entry14_summable_derivBound (2 * n + 1) (by omega)).of_nonneg_of_le
    · exact fun _ ↦ norm_nonneg _
    · intro m
      apply (ContinuousMap.norm_le _ (by
        unfold ch6Entry14_derivBound
        exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          (pow_nonneg (ch6Entry14_apos m).le _))).2
      intro u
      simpa [f] using ch6Entry14_norm_dterm_le (2 * n + 1) m (u : ℝ)
  have hsumContinuous : Continuous (fun u : ℝ ↦
      ∑' m : ℕ, ‖ch6Entry14_dterm (2 * n + 1) u m‖) := by
    apply continuous_tsum (fun m ↦ (ch6Entry14_continuous_dterm (2 * n + 1) m).norm)
      (ch6Entry14_summable_derivBound (2 * n + 1) (by omega))
    intro m u
    simpa only [norm_norm] using ch6Entry14_norm_dterm_le (2 * n + 1) m u
  have hkernelDeriv : ∀ u : ℝ, iteratedDeriv (2 * n + 1) ch6Entry14_kernel u =
      ∑' m : ℕ, ch6Entry14_dterm (2 * n + 1) u m := by
    intro u
    change iteratedDeriv (2 * n + 1) (fun v ↦ -1 / 2 + ch6Entry14_kernelCore v) u = _
    rw [iteratedDeriv_const_add (by omega) (-1 / 2)]
    exact ch6Entry14_iteratedDeriv_kernelCore (2 * n + 1) u
  have hmono :
      (∫ u in (0 : ℝ)..L, ‖iteratedDeriv (2 * n + 1) ch6Entry14_kernel u‖) ≤
        ∫ u in (0 : ℝ)..L, ∑' m : ℕ, ‖ch6Entry14_dterm (2 * n + 1) u m‖ := by
    apply intervalIntegral.integral_mono_on hL
      ((ch6Entry14_contDiff_kernel.continuous_iteratedDeriv (2 * n + 1)
        (WithTop.coe_le_coe.mpr le_top)).norm.intervalIntegrable 0 L)
      (hsumContinuous.intervalIntegrable 0 L)
    intro u _
    rw [hkernelDeriv u]
    exact norm_tsum_le_tsum_norm ((ch6Entry14_summable_dterm (2 * n + 1) (by omega) u).norm)
  have hinterchange :
      (∑' m : ℕ, ∫ u in (0 : ℝ)..L, ‖ch6Entry14_dterm (2 * n + 1) u m‖) =
        ∫ u in (0 : ℝ)..L, ∑' m : ℕ, ‖ch6Entry14_dterm (2 * n + 1) u m‖ := by
    simpa only [f, ContinuousMap.coe_mk] using
      (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsup)
  rw [← hinterchange] at hmono
  have hbound := ch6Entry14_summable_odd_integralBound n hn
  have hint : Summable (fun m : ℕ ↦
      ∫ u in (0 : ℝ)..L, ‖ch6Entry14_dterm (2 * n + 1) u m‖) :=
    hbound.of_nonneg_of_le
      (fun _ ↦ intervalIntegral.integral_nonneg hL fun _ _ ↦ norm_nonneg _)
      (fun m ↦ ch6Entry14_integral_norm_dterm_odd_le m n L hL)
  exact hmono.trans (hint.tsum_le_tsum
    (fun m ↦ ch6Entry14_integral_norm_dterm_odd_le m n L hL) hbound)

private lemma ch6Entry14_tsum_one_div_nat_pow_le_pi_sq_div_six (p : ℕ) (hp : 2 ≤ p) :
    (∑' j : ℕ, 1 / ((j : ℝ) ^ p)) ≤ Real.pi ^ 2 / 6 := by
  have hpSum : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) ^ p)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have htwoSum : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable
  have hle (j : ℕ) : 1 / ((j : ℝ) ^ p) ≤ 1 / ((j : ℝ) ^ 2) := by
    by_cases hj : j = 0
    · simp [hj, zero_pow (by omega : p ≠ 0)]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj)) hp
  rw [← hasSum_zeta_two.tsum_eq]
  exact hpSum.tsum_le_tsum hle htwoSum

private lemma ch6Entry14_bernoulliFun_odd_eq_tsum (n : ℕ) (hn : 1 ≤ n) (y : ℝ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    bernoulliFun (2 * n + 1) y =
      (-1 : ℝ) ^ (n + 1) *
        (2 * ((2 * n + 1).factorial : ℝ) / (2 * Real.pi) ^ (2 * n + 1)) *
          ∑' j : ℕ,
            1 / ((j : ℝ) ^ (2 * n + 1)) *
              Real.sin (2 * Real.pi * j * y) := by
  have hs := (hasSum_one_div_nat_pow_mul_sin (k := n) (by omega) hy).tsum_eq
  rw [show (Polynomial.map (algebraMap ℚ ℝ)
      (Polynomial.bernoulli (2 * n + 1))).eval y =
      bernoulliFun (2 * n + 1) y by rfl] at hs
  rw [hs]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfac : (((2 * n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hsign : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
    rw [← pow_add]
    have he : n + 1 + (n + 1) = 2 * (n + 1) := by omega
    rw [he, pow_mul]
    norm_num
  field_simp [hpi, hfac]
  rw [show ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 by
    simpa only [pow_two] using hsign, mul_one]

private lemma ch6Entry14_abs_bernoulliFun_odd_le (n : ℕ) (hn : 1 ≤ n) (y : ℝ)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * n + 1) y| ≤
      (2 * ((2 * n + 1).factorial : ℝ) / (2 * Real.pi) ^ (2 * n + 1)) *
        (Real.pi ^ 2 / 6) := by
  let g : ℕ → ℝ := fun j ↦
    1 / ((j : ℝ) ^ (2 * n + 1)) * Real.sin (2 * Real.pi * j * y)
  let b : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) ^ (2 * n + 1))
  have hp : 2 ≤ 2 * n + 1 := by omega
  have hb : Summable b := Real.summable_one_div_nat_pow.mpr (by omega)
  have hgb (j : ℕ) : |g j| ≤ b j := by
    unfold g b
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / ((j : ℝ) ^ (2 * n + 1)))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.abs_sin_le_one (2 * Real.pi * j * y)) (by positivity)
  have hgabs : Summable (fun j ↦ |g j|) :=
    hb.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hgb
  have hgnorm : Summable (fun j ↦ ‖g j‖) := by
    simpa only [Real.norm_eq_abs] using hgabs
  have hsum : |∑' j, g j| ≤ Real.pi ^ 2 / 6 := calc
    |∑' j, g j| ≤ ∑' j, |g j| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := g) hgnorm
    _ ≤ ∑' j, b j := hgabs.tsum_le_tsum hgb hb
    _ ≤ Real.pi ^ 2 / 6 := ch6Entry14_tsum_one_div_nat_pow_le_pi_sq_div_six _ hp
  rw [ch6Entry14_bernoulliFun_odd_eq_tsum n hn y hy]
  change |(-1 : ℝ) ^ (n + 1) *
      (2 * ((2 * n + 1).factorial : ℝ) / (2 * Real.pi) ^ (2 * n + 1)) *
        ∑' j, g j| ≤ _
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity :
      0 ≤ 2 * ((2 * n + 1).factorial : ℝ) / (2 * Real.pi) ^ (2 * n + 1))]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

private lemma ch6Entry14_bernoulli_coeff (j : ℕ) :
    ((bernoulli j : ℚ) : ℝ) =
      if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ) := by
  by_cases hj : j = 1
  · subst j
    simp [bernoulli_one]
  · simp [hj]

private lemma ch6Entry14_bernoulliFun_eq_sum (p : ℕ) (x : ℝ) :
    bernoulliFun p x =
      ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
        (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j) := by
  rw [show bernoulliFun p x =
    Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli p)) by rfl]
  rw [Polynomial.bernoulli_def, Polynomial.map_sum, Polynomial.eval_finsetSum]
  have hterm : ∀ i ∈ Finset.range (p + 1),
      Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ)
        (Polynomial.monomial i (bernoulli (p - i) * ↑(p.choose i)))) =
        ((bernoulli (p - i) : ℚ) : ℝ) * (Nat.choose p i : ℝ) * x ^ i := by
    intro i _
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    simp only [map_mul, map_natCast, eq_ratCast]
  rw [Finset.sum_congr rfl hterm]
  have hrefl : (∑ i ∈ Finset.range (p + 1),
      ((bernoulli (p - i) : ℚ) : ℝ) * (Nat.choose p i : ℝ) * x ^ i) =
      ∑ j ∈ Finset.range (p + 1),
        ((bernoulli j : ℚ) : ℝ) * (Nat.choose p (p - j) : ℝ) * x ^ (p - j) := by
    rw [← Finset.sum_range_reflect (fun j ↦ ((bernoulli j : ℚ) : ℝ) *
      (Nat.choose p (p - j) : ℝ) * x ^ (p - j)) (p + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have e1 : p + 1 - 1 - i = p - i := by omega
    have e2 : p - (p - i) = i := by omega
    rw [e1, e2]
  rw [hrefl]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [← ch6Entry14_bernoulli_coeff j, Nat.choose_symm (by omega : j ≤ p)]
  ring

private noncomputable def ch6Entry14_periodicKernel (p : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun p (Int.fract x)

private lemma ch6Entry14_periodicKernel_eq_of_spec
    (P : ℕ → ℝ → ℝ) (p : ℕ)
    (hper : ∀ (m : ℕ) (x : ℝ), P m (x + 1) = P m x)
    (hunit : ∀ x ∈ Set.Ico (0 : ℝ) 1, P p x =
      ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
        (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j))
    (x : ℝ) : P p x = ch6Entry14_periodicKernel p x := by
  have hp : Function.Periodic (P p) 1 := hper p
  have hfract : P p (Int.fract x) = P p x := by
    rw [Int.fract]
    simpa only [mul_one] using hp.sub_int_mul_eq (Int.floor x)
  rw [← hfract, hunit (Int.fract x) ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩]
  exact (ch6Entry14_bernoulliFun_eq_sum p (Int.fract x)).symm

private lemma ch6Entry14_abs_periodicKernel_odd_le (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    |ch6Entry14_periodicKernel (2 * n + 1) x| ≤
      (2 * ((2 * n + 1).factorial : ℝ) / (2 * Real.pi) ^ (2 * n + 1)) *
        (Real.pi ^ 2 / 6) := by
  apply ch6Entry14_abs_bernoulliFun_odd_le n hn
  exact ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

private lemma ch6Entry14_eulerMaclaurin_real
    (a b : ℤ) (p : ℕ) (f : ℝ → ℝ) (hab : a < b) (hp : 1 ≤ p)
    (hdf : ContDiffOn ℝ (p : WithTop ℕ∞) f (Set.Icc (a : ℝ) (b : ℝ))) :
    ∑ j ∈ Finset.Icc a b, f (j : ℝ) =
      (∫ t in (a : ℝ)..(b : ℝ), f t) + (f a + f b) / 2 +
        (∑ k ∈ Finset.Icc 1 (p / 2),
          (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) *
            (iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) b -
              iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) a)) +
        ((-1 : ℝ) ^ (p + 1) / (p.factorial : ℝ) *
          (∫ t in (a : ℝ)..(b : ℝ), ch6Entry14_periodicKernel p t *
            iteratedDerivWithin p f (Set.Icc (a : ℝ) (b : ℝ)) t)) := by
  obtain ⟨P, hper, hunit, hformula⟩ :=
    MetaMathlibExt.eulerMaclaurinFormula a b p f hab hp hdf
  simpa only [ch6Entry14_periodicKernel_eq_of_spec P p hper hunit] using hformula

private lemma ch6Entry14_contDiff_scaledKernel (x : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ ch6Entry14_kernel (x * t)) := by
  exact ch6Entry14_contDiff_kernel.comp (contDiff_const.mul contDiff_id)

private lemma ch6Entry14_iteratedDeriv_scaledKernel (x : ℝ) (q : ℕ) (t : ℝ) :
    iteratedDeriv q (fun s : ℝ ↦ ch6Entry14_kernel (x * s)) t =
      x ^ q * iteratedDeriv q ch6Entry14_kernel (x * t) := by
  have hk : ContDiff ℝ (q : WithTop ℕ∞) ch6Entry14_kernel :=
    ch6Entry14_contDiff_kernel.of_le (WithTop.coe_le_coe.mpr le_top)
  exact congrFun (iteratedDeriv_comp_const_mul hk x) t

private lemma ch6Entry14_iteratedDerivWithin_scaledKernel (x : ℝ) (q J : ℕ)
    (hJ : 1 ≤ J) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) J) :
    iteratedDerivWithin q (fun s : ℝ ↦ ch6Entry14_kernel (x * s)) (Set.Icc (0 : ℝ) J) t =
      x ^ q * iteratedDeriv q ch6Entry14_kernel (x * t) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by exact_mod_cast (Nat.zero_lt_of_lt hJ)))
    ((ch6Entry14_contDiff_scaledKernel x).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) ht]
  exact ch6Entry14_iteratedDeriv_scaledKernel x q t

private lemma ch6Entry14_sum_int_Icc_zero_eq_sum_range (J : ℕ) (f : ℤ → ℝ) :
    ∑ j ∈ Finset.Icc (0 : ℤ) (J : ℤ), f j =
      ∑ j ∈ Finset.range (J + 1), f (j : ℤ) := by
  apply Finset.sum_bij (fun j _ ↦ j.toNat)
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    have hlt : j < (J + 1 : ℕ) :=
      lt_of_le_of_lt hj.2 (by omega : (J : ℤ) < J + 1)
    rw [← Int.toNat_of_nonneg hj.1] at hlt
    exact_mod_cast hlt
  · intro j₁ hj₁ j₂ hj₂ he
    rw [Finset.mem_Icc] at hj₁ hj₂
    rw [← Int.toNat_of_nonneg hj₁.1, ← Int.toNat_of_nonneg hj₂.1, he]
  · intro j hj
    rw [Finset.mem_range] at hj
    refine ⟨(j : ℤ), ?_, by simp⟩
    rw [Finset.mem_Icc]
    exact ⟨by positivity, by exact_mod_cast (Nat.le_of_lt_succ hj)⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Int.toNat_of_nonneg hj.1]

private lemma ch6Entry14_sum_Icc_one_eq_sum_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ j ∈ Finset.range n, f (j + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 n (c := 1)]
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc]

private lemma ch6Entry14_minusCorrection_eq_sum_Icc (n : ℕ) (x : ℝ) :
    chapter6Entry14MinusCorrection n x =
      ∑ k ∈ Finset.Icc 1 n,
        (bernoulli (2 * k) : ℝ) ^ 2 * x ^ (2 * k - 1) /
          ((2 * k : ℝ) * ((2 * k).factorial : ℝ)) := by
  rw [ch6Entry14_sum_Icc_one_eq_sum_range]
  unfold chapter6Entry14MinusCorrection
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  push_cast
  rfl

private noncomputable def ch6Entry14_endpointCorrection (n : ℕ) (x : ℝ) (J : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) *
      (x ^ (2 * k - 1) * iteratedDeriv (2 * k - 1) ch6Entry14_kernel (x * J))

private noncomputable def ch6Entry14_emRemainder (n : ℕ) (x : ℝ) (J : ℕ) : ℝ :=
  1 / ((2 * n + 1).factorial : ℝ) *
    ∫ t in (0 : ℝ)..J, ch6Entry14_periodicKernel (2 * n + 1) t *
      (x ^ (2 * n + 1) * iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t))

private lemma ch6Entry14_remainder_integral_eq_within (n : ℕ) (x : ℝ) (J : ℕ)
    (hJ : 1 ≤ J) :
    (∫ t in (0 : ℝ)..J, ch6Entry14_periodicKernel (2 * n + 1) t *
      iteratedDerivWithin (2 * n + 1) (fun s : ℝ ↦ ch6Entry14_kernel (x * s))
        (Set.Icc (0 : ℝ) J) t) =
      ∫ t in (0 : ℝ)..J, ch6Entry14_periodicKernel (2 * n + 1) t *
        (x ^ (2 * n + 1) * iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t)) := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) J := by
    simpa [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ J)] using ht
  change ch6Entry14_periodicKernel (2 * n + 1) t *
      iteratedDerivWithin (2 * n + 1) (fun s : ℝ ↦ ch6Entry14_kernel (x * s))
        (Set.Icc (0 : ℝ) J) t = _
  rw [ch6Entry14_iteratedDerivWithin_scaledKernel x (2 * n + 1) J hJ ht']

private lemma ch6Entry14_derivative_sum_eq_endpoint_sub_correction
    (n : ℕ) (x : ℝ) (J : ℕ) :
    (∑ k ∈ Finset.Icc 1 n,
      (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) *
        (x ^ (2 * k - 1) * iteratedDeriv (2 * k - 1) ch6Entry14_kernel (x * J) -
          x ^ (2 * k - 1) * iteratedDeriv (2 * k - 1) ch6Entry14_kernel 0)) =
      ch6Entry14_endpointCorrection n x J - chapter6Entry14MinusCorrection n x := by
  rw [ch6Entry14_endpointCorrection, ch6Entry14_minusCorrection_eq_sum_Icc,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [ch6Entry14_iteratedDeriv_kernel_odd_zero k hk.1]
  have hkR : (2 * k : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : 2 * k ≠ 0)
  field_simp [hkR]

private lemma ch6Entry14_finite_eulerMaclaurin_identity
    (x : ℝ) (n J : ℕ) (hn : 1 ≤ n) (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.range (J + 1), ch6Entry14_kernel (x * j) =
      (∫ t in (0 : ℝ)..J, ch6Entry14_kernel (x * t)) +
        (ch6Entry14_kernel 0 + ch6Entry14_kernel (x * J)) / 2 +
        ch6Entry14_endpointCorrection n x J - chapter6Entry14MinusCorrection n x +
        ch6Entry14_emRemainder n x J := by
  let f : ℝ → ℝ := fun t ↦ ch6Entry14_kernel (x * t)
  have hdf : ContDiffOn ℝ ((2 * n + 1 : ℕ) : WithTop ℕ∞) f
      (Set.Icc (0 : ℝ) J) := by
    exact (ch6Entry14_contDiff_scaledKernel x).contDiffOn.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hem := ch6Entry14_eulerMaclaurin_real (0 : ℤ) (J : ℤ) (2 * n + 1) f
    (by exact_mod_cast (Nat.zero_lt_of_lt hJ)) (by omega) (by simpa [f] using hdf)
  rw [ch6Entry14_sum_int_Icc_zero_eq_sum_range] at hem
  simp only [Int.cast_zero, Int.cast_natCast] at hem
  have hderJ (q : ℕ) :
      iteratedDerivWithin q f (Set.Icc (0 : ℝ) J) J =
        x ^ q * iteratedDeriv q ch6Entry14_kernel (x * J) := by
    simpa [f] using ch6Entry14_iteratedDerivWithin_scaledKernel x q J hJ (t := (J : ℝ)) (by simp)
  have hder0 (q : ℕ) :
      iteratedDerivWithin q f (Set.Icc (0 : ℝ) J) 0 =
        x ^ q * iteratedDeriv q ch6Entry14_kernel 0 := by
    simpa [f] using ch6Entry14_iteratedDerivWithin_scaledKernel x q J hJ (t := (0 : ℝ)) (by simp)
  simp_rw [hderJ, hder0] at hem
  rw [show (2 * n + 1) / 2 = n by omega] at hem
  have hderiv := ch6Entry14_derivative_sum_eq_endpoint_sub_correction n x J
  rw [hderiv] at hem
  have hrem := ch6Entry14_remainder_integral_eq_within n x J hJ
  rw [hrem] at hem
  have hsign : (-1 : ℝ) ^ (2 * n + 1 + 1) = 1 := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, pow_mul]
    norm_num
  rw [hsign, one_div] at hem
  simpa [f, ch6Entry14_emRemainder, mul_assoc, sub_eq_add_neg, add_assoc] using hem

private lemma ch6Entry14_tsum_one_div_succ_pow_le_pi_sq_div_six (p : ℕ) (hp : 2 ≤ p) :
    (∑' j : ℕ, 1 / (((j + 1 : ℕ) : ℝ) ^ p)) ≤ Real.pi ^ 2 / 6 := by
  have hs : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) ^ p)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hdecomp := hs.sum_add_tsum_nat_add 1
  have hp0 : p ≠ 0 := by omega
  have hprefix : (∑ j ∈ Finset.range 1, 1 / ((j : ℝ) ^ p)) = 0 := by
    simp [zero_pow hp0]
  rw [hprefix, zero_add] at hdecomp
  have heq : (∑' j : ℕ, 1 / (((j + 1 : ℕ) : ℝ) ^ p)) =
      ∑' j : ℕ, 1 / ((j : ℝ) ^ p) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using hdecomp
  rw [heq]
  exact ch6Entry14_tsum_one_div_nat_pow_le_pi_sq_div_six p hp

private lemma ch6Entry14_tsum_odd_integralBound_le (n : ℕ) (hn : 1 ≤ n) :
    (∑' m : ℕ,
      Real.pi * ((2 * n + 1).factorial : ℝ) / ch6Entry14_aterm m ^ (2 * n + 1)) ≤
      (Real.pi * ((2 * n + 1).factorial : ℝ) /
        (2 * Real.pi) ^ (2 * n + 1)) * (Real.pi ^ 2 / 6) := by
  let C : ℝ := Real.pi * ((2 * n + 1).factorial : ℝ) /
    (2 * Real.pi) ^ (2 * n + 1)
  have hterm : ∀ m : ℕ,
      Real.pi * ((2 * n + 1).factorial : ℝ) / ch6Entry14_aterm m ^ (2 * n + 1) =
        C * (1 / (((m + 1 : ℕ) : ℝ) ^ (2 * n + 1))) := by
    intro m
    unfold C ch6Entry14_aterm
    push_cast
    rw [mul_pow]
    field_simp
  rw [tsum_congr hterm, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left
    (ch6Entry14_tsum_one_div_succ_pow_le_pi_sq_div_six (2 * n + 1) (by omega)) (by
      unfold C
      positivity)

private noncomputable def ch6Entry14_periodicOddBound (n : ℕ) : ℝ :=
  (2 * ((2 * n + 1).factorial : ℝ) / (2 * Real.pi) ^ (2 * n + 1)) *
    (Real.pi ^ 2 / 6)

private noncomputable def ch6Entry14_integralOddBound (n : ℕ) : ℝ :=
  (Real.pi * ((2 * n + 1).factorial : ℝ) /
    (2 * Real.pi) ^ (2 * n + 1)) * (Real.pi ^ 2 / 6)

private noncomputable def ch6Entry14_coarseRemainderBound (n : ℕ) (x : ℝ) : ℝ :=
  (1 / ((2 * n + 1).factorial : ℝ)) * ch6Entry14_periodicOddBound n *
    x ^ (2 * n) * ch6Entry14_integralOddBound n

private lemma ch6Entry14_periodicOddBound_nonneg (n : ℕ) : 0 ≤ ch6Entry14_periodicOddBound n := by
  unfold ch6Entry14_periodicOddBound
  positivity

private lemma ch6Entry14_scaled_derivative_integral_le (n J : ℕ) (x : ℝ)
    (hn : 1 ≤ n) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..J, ‖iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t)‖) ≤
      x⁻¹ * ch6Entry14_integralOddBound n := by
  have hscale := intervalIntegral.integral_comp_mul_left
    (fun u : ℝ ↦ ‖iteratedDeriv (2 * n + 1) ch6Entry14_kernel u‖) hx.ne'
    (a := (0 : ℝ)) (b := (J : ℝ))
  have hscale' :
      (∫ t in (0 : ℝ)..J, ‖iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t)‖) =
        x⁻¹ * ∫ u in (0 : ℝ)..x * J,
          ‖iteratedDeriv (2 * n + 1) ch6Entry14_kernel u‖ := by
    simpa [smul_eq_mul] using hscale
  rw [hscale']
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hx.le)
  exact (ch6Entry14_integral_norm_iteratedDeriv_kernel_odd_le n (x * J) hn (by positivity)).trans
    (by simpa [ch6Entry14_integralOddBound] using ch6Entry14_tsum_odd_integralBound_le n hn)

private lemma ch6Entry14_abs_emRemainder_le (n J : ℕ) (x : ℝ)
    (hn : 1 ≤ n) (hx : 0 < x) :
    |ch6Entry14_emRemainder n x J| ≤ ch6Entry14_coarseRemainderBound n x := by
  let g : ℝ → ℝ := fun t ↦ ch6Entry14_periodicOddBound n *
    (x ^ (2 * n + 1) * ‖iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t)‖)
  have hgContinuous : Continuous g := by
    unfold g
    exact continuous_const.mul (continuous_const.mul
      (((ch6Entry14_contDiff_kernel.continuous_iteratedDeriv (2 * n + 1)
        (WithTop.coe_le_coe.mpr le_top)).norm).comp
          (continuous_const.mul continuous_id)))
  have hint :
      ‖∫ t in (0 : ℝ)..J, ch6Entry14_periodicKernel (2 * n + 1) t *
        (x ^ (2 * n + 1) * iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t))‖ ≤
        ∫ t in (0 : ℝ)..J, g t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by positivity)
      (by
        filter_upwards with t
        intro _
        change ‖ch6Entry14_periodicKernel (2 * n + 1) t *
          (x ^ (2 * n + 1) * iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t))‖ ≤ g t
        rw [norm_mul, norm_mul]
        simp only [Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg hx.le (2 * n + 1))]
        exact mul_le_mul_of_nonneg_right
          (ch6Entry14_abs_periodicKernel_odd_le n hn t) (by positivity))
      (hgContinuous.intervalIntegrable 0 J)
  have hgIntegral :
      (∫ t in (0 : ℝ)..J, g t) =
        ch6Entry14_periodicOddBound n * x ^ (2 * n + 1) *
          ∫ t in (0 : ℝ)..J, ‖iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t)‖ := by
    unfold g
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [ch6Entry14_emRemainder, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 1 / ((2 * n + 1).factorial : ℝ))]
  calc
    1 / ((2 * n + 1).factorial : ℝ) *
        |∫ t in (0 : ℝ)..J, ch6Entry14_periodicKernel (2 * n + 1) t *
          (x ^ (2 * n + 1) * iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t))| ≤
      1 / ((2 * n + 1).factorial : ℝ) * (∫ t in (0 : ℝ)..J, g t) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hint) (by positivity)
    _ = 1 / ((2 * n + 1).factorial : ℝ) * ch6Entry14_periodicOddBound n *
        x ^ (2 * n + 1) *
          (∫ t in (0 : ℝ)..J, ‖iteratedDeriv (2 * n + 1) ch6Entry14_kernel (x * t)‖) := by
      rw [hgIntegral]
      ring
    _ ≤ 1 / ((2 * n + 1).factorial : ℝ) * ch6Entry14_periodicOddBound n *
        x ^ (2 * n + 1) * (x⁻¹ * ch6Entry14_integralOddBound n) :=
      mul_le_mul_of_nonneg_left (ch6Entry14_scaled_derivative_integral_le n J x hn hx)
        (mul_nonneg
          (mul_nonneg (by positivity) (ch6Entry14_periodicOddBound_nonneg n))
          (pow_nonneg hx.le _))
    _ = ch6Entry14_coarseRemainderBound n x := by
      unfold ch6Entry14_coarseRemainderBound
      have hxPow : x ^ (2 * n + 1) = x ^ (2 * n) * x := by
        rw [pow_succ]
      rw [hxPow]
      field_simp [hx.ne']

private lemma ch6Entry14_one_le_tsum_one_div_succ_even_pow (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ ∑' m : ℕ, 1 / (((m + 1 : ℕ) : ℝ) ^ (2 * k)) := by
  have hs : Summable (fun m : ℕ ↦
      1 / (((m + 1 : ℕ) : ℝ) ^ (2 * k))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by omega))
  simpa using hs.le_tsum 0 (fun _ _ ↦ by positivity)

private lemma ch6Entry14_abs_bernoulli_even_eq_tsum (k : ℕ) (hk : 1 ≤ k) :
    |(bernoulli (2 * k) : ℝ)| =
      (2 * ((2 * k).factorial : ℝ) / (2 * Real.pi) ^ (2 * k)) *
        ∑' m : ℕ, 1 / (((m + 1 : ℕ) : ℝ) ^ (2 * k)) := by
  let T : ℝ := ∑' m : ℕ, 1 / (((m + 1 : ℕ) : ℝ) ^ (2 * k))
  have hT := ch6Entry14_tsum_one_div_succ_pow k hk
  have hTnonneg : 0 ≤ T := tsum_nonneg fun _ ↦ by positivity
  have hsign : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ (k + 1) = 1 := by
    rw [← pow_add]
    have he : k + 1 + (k + 1) = 2 * (k + 1) := by omega
    rw [he, pow_mul]
    norm_num
  have hB : (bernoulli (2 * k) : ℝ) =
      (-1 : ℝ) ^ (k + 1) *
        (2 * ((2 * k).factorial : ℝ) / (2 * Real.pi) ^ (2 * k)) * T := by
    change T = _ at hT
    rw [hT]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hfac : (((2 * k).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hpi, hfac]
    rw [show ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 by
      simpa only [pow_two] using hsign, mul_one]
    rw [mul_pow]
    rw [show (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) by
      have he : 2 * k = (2 * k - 1) + 1 := by omega
      have hp : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ ((2 * k - 1) + 1) :=
        congr_arg (fun t : ℕ ↦ (2 : ℝ) ^ t) he
      rw [hp, pow_succ]
      ring]
    ring
  rw [hB, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity :
      0 ≤ 2 * ((2 * k).factorial : ℝ) / (2 * Real.pi) ^ (2 * k)),
    abs_of_nonneg hTnonneg]

private lemma ch6Entry14_abs_bernoulli_even_lower (k : ℕ) (hk : 1 ≤ k) :
    2 * ((2 * k).factorial : ℝ) / (2 * Real.pi) ^ (2 * k) ≤
      |(bernoulli (2 * k) : ℝ)| := by
  rw [ch6Entry14_abs_bernoulli_even_eq_tsum k hk]
  exact le_mul_of_one_le_right (by positivity)
    (ch6Entry14_one_le_tsum_one_div_succ_even_pow k hk)

private lemma ch6Entry14_pi_mul_pi_sq_div_six_le_eight :
    Real.pi * (Real.pi ^ 2 / 6) ≤ 8 := by
  have hpi : Real.pi ≤ (7 / 2 : ℝ) := by
    linarith [Real.pi_lt_d2]
  have hcub : Real.pi ^ 3 ≤ (7 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left₀ Real.pi_nonneg hpi 3
  calc
    Real.pi * (Real.pi ^ 2 / 6) = Real.pi ^ 3 / 6 := by ring
    _ ≤ (7 / 2 : ℝ) ^ 3 / 6 := by gcongr
    _ ≤ 8 := by norm_num

private lemma ch6Entry14_coarseRemainderBound_eq (n : ℕ) (x : ℝ) :
    ch6Entry14_coarseRemainderBound n x =
      (2 * Real.pi * ((2 * n + 1).factorial : ℝ) * (Real.pi ^ 2 / 6) ^ 2) *
        x ^ (2 * n) / (2 * Real.pi) ^ (4 * n + 2) := by
  unfold ch6Entry14_coarseRemainderBound ch6Entry14_periodicOddBound ch6Entry14_integralOddBound
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring

private lemma ch6Entry14_coarse_coefficient_le (n : ℕ) (hn : 1 ≤ n) :
    2 * Real.pi * ((2 * n + 1).factorial : ℝ) * (Real.pi ^ 2 / 6) ^ 2 ≤
      4 * ((2 * n + 2).factorial : ℝ) * (Real.pi ^ 2 / 6) := by
  have hindex : (8 : ℝ) ≤ 2 * (2 * n + 2 : ℕ) := by
    norm_cast
    omega
  have hpiZ : Real.pi * (Real.pi ^ 2 / 6) ≤ 2 * (2 * n + 2 : ℕ) :=
    ch6Entry14_pi_mul_pi_sq_div_six_le_eight.trans hindex
  calc
    2 * Real.pi * ((2 * n + 1).factorial : ℝ) * (Real.pi ^ 2 / 6) ^ 2 =
        (2 * ((2 * n + 1).factorial : ℝ) * (Real.pi ^ 2 / 6)) *
          (Real.pi * (Real.pi ^ 2 / 6)) := by ring
    _ ≤ (2 * ((2 * n + 1).factorial : ℝ) * (Real.pi ^ 2 / 6)) *
        (2 * (2 * n + 2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hpiZ (by positivity)
    _ = 4 * ((2 * n + 2).factorial : ℝ) * (Real.pi ^ 2 / 6) := by
      have hfacNat : (2 * n + 2).factorial =
          (2 * n + 2) * (2 * n + 1).factorial := by
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ]
      have hfac : (((2 * n + 2).factorial : ℕ) : ℝ) =
          (2 * n + 2 : ℕ) * ((2 * n + 1).factorial : ℝ) := by
        exact_mod_cast hfacNat
      rw [hfac]
      push_cast
      ring

private lemma ch6Entry14_bernoulli_product_lower (n : ℕ) (hn : 1 ≤ n) :
    4 * ((2 * n).factorial : ℝ) * ((2 * n + 2).factorial : ℝ) /
        (2 * Real.pi) ^ (4 * n + 2) ≤
      |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| := by
  have h₁ := ch6Entry14_abs_bernoulli_even_lower n hn
  have h₂ := ch6Entry14_abs_bernoulli_even_lower (n + 1) (by omega)
  have hprod :
      (2 * ((2 * n).factorial : ℝ) / (2 * Real.pi) ^ (2 * n)) *
          (2 * ((2 * (n + 1)).factorial : ℝ) /
            (2 * Real.pi) ^ (2 * (n + 1))) ≤
        |(bernoulli (2 * n) : ℝ)| * |(bernoulli (2 * (n + 1)) : ℝ)| :=
    mul_le_mul h₁ h₂ (by positivity) (abs_nonneg _)
  rw [← abs_mul] at hprod
  convert hprod using 1
  field_simp [Real.pi_ne_zero]
  ring_nf

private lemma ch6Entry14_coarseRemainderBound_le_frozen (n : ℕ) (x : ℝ)
    (hn : 1 ≤ n) :
    ch6Entry14_coarseRemainderBound n x ≤
      |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
        x ^ (2 * n) / ((2 * n).factorial : ℝ) * (Real.pi ^ 2 / 6) := by
  let D : ℝ := (2 * Real.pi) ^ (4 * n + 2)
  let X : ℝ := x ^ (2 * n)
  let Z : ℝ := Real.pi ^ 2 / 6
  have hD : 0 < D := by unfold D; positivity
  have hX : 0 ≤ X := by
    unfold X
    rw [pow_mul]
    positivity
  have hZ : 0 ≤ Z := by unfold Z; positivity
  have hfac : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
  rw [ch6Entry14_coarseRemainderBound_eq]
  change (2 * Real.pi * ((2 * n + 1).factorial : ℝ) * Z ^ 2) * X / D ≤ _
  calc
    (2 * Real.pi * ((2 * n + 1).factorial : ℝ) * Z ^ 2) * X / D ≤
        (4 * ((2 * n + 2).factorial : ℝ) * Z) * X / D := by
      apply div_le_div_of_nonneg_right _ hD.le
      exact mul_le_mul_of_nonneg_right
        (by simpa [Z] using ch6Entry14_coarse_coefficient_le n hn) hX
    _ = (4 * ((2 * n).factorial : ℝ) * ((2 * n + 2).factorial : ℝ) / D) *
        X / ((2 * n).factorial : ℝ) * Z := by
      field_simp
    _ ≤ |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
        X / ((2 * n).factorial : ℝ) * Z := by
      have hp := ch6Entry14_bernoulli_product_lower n hn
      have hmult : 0 ≤ X / ((2 * n).factorial : ℝ) * Z := by positivity
      calc
        (4 * ((2 * n).factorial : ℝ) * ((2 * n + 2).factorial : ℝ) / D) *
            X / ((2 * n).factorial : ℝ) * Z =
          (4 * ((2 * n).factorial : ℝ) * ((2 * n + 2).factorial : ℝ) / D) *
            (X / ((2 * n).factorial : ℝ) * Z) := by ring
        _ ≤ |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
            (X / ((2 * n).factorial : ℝ) * Z) :=
          mul_le_mul_of_nonneg_right (by simpa [D] using hp) hmult
        _ = _ := by ring
    _ = _ := by rfl

private noncomputable def ch6Entry14_kernelAntiderivative (u : ℝ) : ℝ :=
  Real.log (1 - Real.exp (-u)) - Real.log u

private lemma ch6Entry14_tendsto_kernelAntiderivative_zero_right :
    Tendsto ch6Entry14_kernelAntiderivative (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hslope := (Real.hasDerivAt_exp 0).tendsto_slope_zero_right
  have hbasic : Tendsto (fun u : ℝ ↦ (Real.exp u - 1) / u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [smul_eq_mul, div_eq_inv_mul] using hslope
  have hexp : Tendsto Real.exp (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : Tendsto Real.exp (nhds (0 : ℝ)) (nhds (Real.exp 0)) :=
      Real.continuous_exp.continuousAt.tendsto
    change Tendsto Real.exp (nhds 0 ⊓ Filter.principal (Set.Ioi 0)) (nhds 1)
    simpa using h.mono_left inf_le_left
  have hratio : Tendsto (fun u : ℝ ↦ (1 - Real.exp (-u)) / u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hquot := hbasic.div hexp one_ne_zero
    have hquot' : Tendsto ((fun u : ℝ ↦ (Real.exp u - 1) / u) / Real.exp)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by simpa using hquot
    apply hquot'.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    change 0 < u at hu
    symm
    change (1 - Real.exp (-u)) / u = ((Real.exp u - 1) / u) / Real.exp u
    rw [Real.exp_neg]
    field_simp [hu.ne', Real.exp_ne_zero]
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  have hlog' : Tendsto (Real.log ∘ fun u : ℝ ↦ (1 - Real.exp (-u)) / u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by simpa using hlog
  apply hlog'.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  change 0 < u at hu
  change Real.log ((1 - Real.exp (-u)) / u) = ch6Entry14_kernelAntiderivative u
  rw [ch6Entry14_kernelAntiderivative, Real.log_div]
  · have he : Real.exp (-u) < 1 := by
      rw [Real.exp_neg, inv_lt_one₀ (Real.exp_pos u)]
      exact Real.one_lt_exp_iff.mpr hu
    exact (sub_pos.mpr he).ne'
  · exact hu.ne'

private lemma ch6Entry14_hasDerivAt_kernelAntiderivative {u : ℝ} (hu : 0 < u) :
    HasDerivAt ch6Entry14_kernelAntiderivative (ch6Entry14_kernel u) u := by
  have hexp : HasDerivAt (fun v : ℝ ↦ Real.exp (-v)) (-Real.exp (-u)) u :=
    by convert (hasDerivAt_id u).neg.exp using 1 <;> simp
  have hinner : HasDerivAt (fun v : ℝ ↦ 1 - Real.exp (-v)) (Real.exp (-u)) u := by
    convert (hasDerivAt_const u (1 : ℝ)).sub hexp using 1
    ring
  have hinnerPos : 0 < 1 - Real.exp (-u) := by
    rw [sub_pos, Real.exp_neg, inv_lt_one₀ (Real.exp_pos u)]
    exact Real.one_lt_exp_iff.mpr hu
  have hlogInner := (Real.hasDerivAt_log hinnerPos.ne').comp u hinner
  have hlogU := Real.hasDerivAt_log hu.ne'
  have hderiv := hlogInner.sub hlogU
  apply hderiv.congr_deriv
  rw [ch6Entry14_kernel_eq u hu.ne']
  rw [Real.exp_neg]
  have he : Real.exp u ≠ 0 := Real.exp_ne_zero u
  have he1 : Real.exp u - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact (Real.exp_eq_one_iff u).not.mpr hu.ne'
  field_simp [he, he1, hu.ne']

private lemma ch6Entry14_integral_kernel_eq (L : ℝ) (hL : 0 < L) :
    ∫ u in (0 : ℝ)..L, ch6Entry14_kernel u = ch6Entry14_kernelAntiderivative L := by
  have hderiv : ∀ u ∈ Set.Ioo (0 : ℝ) L,
      HasDerivAt ch6Entry14_kernelAntiderivative (ch6Entry14_kernel u) u :=
    fun u hu ↦ ch6Entry14_hasDerivAt_kernelAntiderivative hu.1
  have hint : IntervalIntegrable ch6Entry14_kernel MeasureTheory.volume 0 L :=
    ch6Entry14_contDiff_kernel.continuous.intervalIntegrable 0 L
  have hright : Tendsto ch6Entry14_kernelAntiderivative (nhdsWithin L (Set.Iio L))
      (nhds (ch6Entry14_kernelAntiderivative L)) :=
    (ch6Entry14_hasDerivAt_kernelAntiderivative hL).continuousAt.tendsto.mono_left inf_le_left
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hL hderiv hint
    ch6Entry14_tendsto_kernelAntiderivative_zero_right hright

private lemma ch6Entry14_integral_scaledKernel_eq (x : ℝ) (J : ℕ)
    (hx : 0 < x) (hJ : 1 ≤ J) :
    ∫ t in (0 : ℝ)..J, ch6Entry14_kernel (x * t) =
      x⁻¹ * ch6Entry14_kernelAntiderivative (x * J) := by
  rw [intervalIntegral.integral_comp_mul_left (fun u : ℝ ↦ ch6Entry14_kernel u) hx.ne']
  simp only [smul_eq_mul, mul_zero]
  rw [ch6Entry14_integral_kernel_eq (x * J) (by positivity)]

private lemma ch6Entry14_tendsto_kernel_atTop : Tendsto ch6Entry14_kernel atTop (nhds 0) := by
  have hneg := Real.tendsto_exp_neg_atTop_nhds_zero
  have hden : Tendsto (fun u : ℝ ↦ 1 - Real.exp (-u)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hneg
  have hquot : Tendsto (fun u : ℝ ↦ Real.exp (-u) / (1 - Real.exp (-u)))
      atTop (nhds 0) := by
    have heq : ((fun u : ℝ ↦ Real.exp (-u)) /
        (fun u : ℝ ↦ 1 - Real.exp (-u))) =
        (fun u : ℝ ↦ Real.exp (-u) / (1 - Real.exp (-u))) := by rfl
    rw [← heq]
    simpa using hneg.div hden one_ne_zero
  have hfirst : Tendsto (fun u : ℝ ↦ 1 / (Real.exp u - 1)) atTop (nhds 0) := by
    apply hquot.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [Real.exp_neg]
    have he : Real.exp u ≠ 0 := Real.exp_ne_zero u
    have he1 : Real.exp u - 1 ≠ 0 := by
      rw [sub_ne_zero]
      exact (Real.exp_eq_one_iff u).not.mpr hu.ne'
    field_simp [he, he1]
  have hinv : Tendsto (fun u : ℝ ↦ 1 / u) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun u : ℝ ↦ u⁻¹) atTop (nhds 0))
  have hsub := hfirst.sub hinv
  have hsub' : Tendsto (fun u : ℝ ↦ 1 / (Real.exp u - 1) - 1 / u)
      atTop (nhds 0) := by simpa using hsub
  apply hsub'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  exact (ch6Entry14_kernel_eq u hu.ne').symm

private lemma ch6Entry14_tendsto_dterm_odd_atTop (n m : ℕ) :
    Tendsto (fun u : ℝ ↦ ch6Entry14_dterm (2 * n + 1) u m) atTop (nhds 0) := by
  let A : ℝ := 2 * ((2 * n + 1).factorial : ℝ)
  have hupper : Tendsto (fun u : ℝ ↦ A * u⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_inv_atTop_zero : Tendsto (fun u : ℝ ↦ u⁻¹) atTop (nhds 0)).pow 2)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      calc
        ‖ch6Entry14_dterm (2 * n + 1) u m‖ ≤
            A / (u ^ 2 + ch6Entry14_aterm m ^ 2) ^ (n + 1) := ch6Entry14_norm_dterm_odd_le m n u
        _ ≤ A / u ^ 2 := by
          apply div_le_div_of_nonneg_left (by unfold A; positivity) (by positivity)
          have hbase : 1 ≤ u ^ 2 + ch6Entry14_aterm m ^ 2 := by
            nlinarith [sq_nonneg (ch6Entry14_aterm m)]
          have hpw : u ^ 2 + ch6Entry14_aterm m ^ 2 ≤
              (u ^ 2 + ch6Entry14_aterm m ^ 2) ^ (n + 1) := by
            simpa only [pow_one] using
              (pow_le_pow_right₀ hbase (by omega : 1 ≤ n + 1))
          exact (le_add_of_nonneg_right (sq_nonneg (ch6Entry14_aterm m))).trans
            hpw
        _ = A * u⁻¹ ^ 2 := by rw [inv_pow]; ring)
    hupper

private lemma ch6Entry14_tendsto_iteratedDeriv_kernel_odd_atTop (n : ℕ) :
    Tendsto (fun u : ℝ ↦ iteratedDeriv (2 * n + 1) ch6Entry14_kernel u) atTop (nhds 0) := by
  have htsum : Tendsto (fun u : ℝ ↦ ∑' m : ℕ, ch6Entry14_dterm (2 * n + 1) u m)
      atTop (nhds 0) := by
    simpa using tendsto_tsum_of_dominated_convergence
      (ch6Entry14_summable_derivBound (2 * n + 1) (by omega))
      (fun m ↦ ch6Entry14_tendsto_dterm_odd_atTop n m)
      (Eventually.of_forall fun u m ↦ ch6Entry14_norm_dterm_le (2 * n + 1) m u)
  apply htsum.congr'
  apply Eventually.of_forall
  intro u
  symm
  change iteratedDeriv (2 * n + 1) (fun v ↦ -1 / 2 + ch6Entry14_kernelCore v) u = _
  rw [iteratedDeriv_const_add (by omega) (-1 / 2)]
  exact ch6Entry14_iteratedDeriv_kernelCore (2 * n + 1) u

private lemma ch6Entry14_tendsto_kernel_nat_scale_atTop (x : ℝ) (hx : 0 < x) :
    Tendsto (fun J : ℕ ↦ ch6Entry14_kernel (x * J)) atTop (nhds 0) :=
  ch6Entry14_tendsto_kernel_atTop.comp
    ((tendsto_natCast_atTop_atTop : Tendsto (fun J : ℕ ↦ (J : ℝ)) atTop atTop).const_mul_atTop hx)

private lemma ch6Entry14_tendsto_endpointCorrection_atTop (n : ℕ) (x : ℝ)
    (hx : 0 < x) :
    Tendsto (fun J : ℕ ↦ ch6Entry14_endpointCorrection n x J) atTop (nhds 0) := by
  unfold ch6Entry14_endpointCorrection
  have hs : Tendsto
      (fun J : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
        (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) *
          (x ^ (2 * k - 1) * iteratedDeriv (2 * k - 1) ch6Entry14_kernel (x * J)))
      atTop (nhds (∑ _k ∈ Finset.Icc 1 n, (0 : ℝ))) := by
    apply tendsto_finsetSum (Finset.Icc 1 n)
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hindex : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
    have hd : Tendsto
        (fun J : ℕ ↦ iteratedDeriv (2 * k - 1) ch6Entry14_kernel (x * J)) atTop (nhds 0) := by
      rw [hindex]
      exact (ch6Entry14_tendsto_iteratedDeriv_kernel_odd_atTop (k - 1)).comp
        ((tendsto_natCast_atTop_atTop :
          Tendsto (fun J : ℕ ↦ (J : ℝ)) atTop atTop).const_mul_atTop hx)
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.mul hd))
  simpa using hs

private lemma ch6Entry14_tendsto_log_one_sub_exp_neg_nat_scale (x : ℝ) (hx : 0 < x) :
    Tendsto (fun J : ℕ ↦ Real.log (1 - Real.exp (-(x * J)))) atTop (nhds 0) := by
  have hscale : Tendsto (fun J : ℕ ↦ x * (J : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun J : ℕ ↦ (J : ℝ)) atTop atTop).const_mul_atTop hx
  have hexp : Tendsto (fun J : ℕ ↦ Real.exp (-(x * J))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hinner : Tendsto (fun J : ℕ ↦ 1 - Real.exp (-(x * J))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hexp
  have hlog : Tendsto (Real.log ∘ fun J : ℕ ↦ 1 - Real.exp (-(x * J)))
      atTop (nhds 0) := by
    simpa only [Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hinner
  apply hlog.congr'
  exact Eventually.of_forall fun _ ↦ rfl

private lemma ch6Entry14_tendsto_bulkTerm_atTop (x : ℝ) (hx : 0 < x) :
    Tendsto (fun J : ℕ ↦
      (∫ t in (0 : ℝ)..J, ch6Entry14_kernel (x * t)) + ((harmonic J : ℚ) : ℝ) / x)
      atTop (nhds ((Real.eulerMascheroniConstant - Real.log x) / x)) := by
  have hmain := Real.tendsto_harmonic_sub_log
  have hsmall := ch6Entry14_tendsto_log_one_sub_exp_neg_nat_scale x hx
  have hcombined : Tendsto (fun J : ℕ ↦
      ((((harmonic J : ℚ) : ℝ) - Real.log (J : ℝ)) - Real.log x +
        Real.log (1 - Real.exp (-(x * J)))) / x) atTop
      (nhds ((Real.eulerMascheroniConstant - Real.log x) / x)) := by
    simpa [sub_eq_add_neg, add_assoc] using
      ((hmain.sub_const (Real.log x)).add hsmall).div_const x
  apply hcombined.congr'
  filter_upwards [eventually_ge_atTop 1] with J hJ
  symm
  rw [ch6Entry14_integral_scaledKernel_eq x J hx hJ]
  unfold ch6Entry14_kernelAntiderivative
  rw [Real.log_mul hx.ne' (by positivity : (J : ℝ) ≠ 0)]
  field_simp [hx.ne']
  ring

private lemma ch6Entry14_minusTerm_eq_kernel_add (x : ℝ) (hx : 0 < x) (j : ℕ) :
    chapter6Entry14MinusTerm x j =
      ch6Entry14_kernel (x * ((j + 1 : ℕ) : ℝ)) + 1 / (x * ((j + 1 : ℕ) : ℝ)) := by
  have hu : 0 < x * ((j + 1 : ℕ) : ℝ) := by positivity
  rw [chapter6Entry14MinusTerm]
  simp only [Nat.cast_add, Nat.cast_one] at hu ⊢
  rw [ch6Entry14_kernel_eq (x * ((j : ℝ) + 1)) hu.ne']
  rw [mul_comm ((j : ℝ) + 1) x]
  ring_nf

private lemma ch6Entry14_sum_one_div_scale_eq_harmonic (x : ℝ) (hx : 0 < x) (J : ℕ) :
    ∑ j ∈ Finset.range J, 1 / (x * ((j + 1 : ℕ) : ℝ)) =
      ((harmonic J : ℚ) : ℝ) / x := by
  rw [harmonic, Rat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Rat.cast_inv, Rat.cast_natCast]
  push_cast
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hx.ne', hj]

private lemma ch6Entry14_partialSum_minusTerm_eq (x : ℝ) (hx : 0 < x) (J : ℕ) :
    ∑ j ∈ Finset.range J, chapter6Entry14MinusTerm x j =
      (∑ j ∈ Finset.range (J + 1), ch6Entry14_kernel (x * j)) - ch6Entry14_kernel 0 +
        ((harmonic J : ℚ) : ℝ) / x := by
  simp_rw [ch6Entry14_minusTerm_eq_kernel_add x hx]
  rw [Finset.sum_add_distrib, ch6Entry14_sum_one_div_scale_eq_harmonic x hx J,
    Finset.sum_range_succ']
  ring_nf

private noncomputable def ch6Entry14_minusMain (n : ℕ) (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant / x - Real.log x / x + 1 / 4 -
    chapter6Entry14MinusCorrection n x

private lemma ch6Entry14_finite_error_identity (x : ℝ) (n J : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n) (hJ : 1 ≤ J) :
    (∑ j ∈ Finset.range J, chapter6Entry14MinusTerm x j) - ch6Entry14_minusMain n x =
      ((∫ t in (0 : ℝ)..J, ch6Entry14_kernel (x * t)) + ((harmonic J : ℚ) : ℝ) / x -
        ((Real.eulerMascheroniConstant - Real.log x) / x)) +
      ch6Entry14_kernel (x * J) / 2 + ch6Entry14_endpointCorrection n x J +
        ch6Entry14_emRemainder n x J := by
  rw [ch6Entry14_partialSum_minusTerm_eq x hx J,
    ch6Entry14_finite_eulerMaclaurin_identity x n J hn hJ, ch6Entry14_kernel_zero]
  unfold ch6Entry14_minusMain
  ring

private lemma ch6Entry14_tendsto_emRemainder_atTop (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n) (hs : Summable (chapter6Entry14MinusTerm x)) :
    Tendsto (fun J : ℕ ↦ ch6Entry14_emRemainder n x J) atTop
      (nhds (chapter6Entry14MinusSum x - ch6Entry14_minusMain n x)) := by
  have hpartial : Tendsto
      (fun J : ℕ ↦ (∑ j ∈ Finset.range J, chapter6Entry14MinusTerm x j) -
        ch6Entry14_minusMain n x) atTop
      (nhds (chapter6Entry14MinusSum x - ch6Entry14_minusMain n x)) := by
    exact hs.hasSum.tendsto_sum_nat.sub_const (ch6Entry14_minusMain n x)
  have hbulk : Tendsto (fun J : ℕ ↦
      ((∫ t in (0 : ℝ)..J, ch6Entry14_kernel (x * t)) + ((harmonic J : ℚ) : ℝ) / x -
        ((Real.eulerMascheroniConstant - Real.log x) / x))) atTop (nhds 0) := by
    simpa using (ch6Entry14_tendsto_bulkTerm_atTop x hx).sub_const
      ((Real.eulerMascheroniConstant - Real.log x) / x)
  have hkernel : Tendsto (fun J : ℕ ↦ ch6Entry14_kernel (x * J) / 2) atTop (nhds 0) := by
    simpa using (ch6Entry14_tendsto_kernel_nat_scale_atTop x hx).div_const 2
  have hendpoint := ch6Entry14_tendsto_endpointCorrection_atTop n x hx
  have hlimit := ((hpartial.sub hbulk).sub hkernel).sub hendpoint
  simp only [sub_zero] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop 1] with J hJ
  rw [ch6Entry14_finite_error_identity x n J hx hn hJ]
  ring_nf

private lemma ch6Entry14_minus_asymptotic_bound (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n) (hs : Summable (chapter6Entry14MinusTerm x)) :
    |chapter6Entry14MinusSum x - ch6Entry14_minusMain n x| ≤
      |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
        x ^ (2 * n) / ((2 * n).factorial : ℝ) *
          (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6) := by
  have hcoarse : |chapter6Entry14MinusSum x - ch6Entry14_minusMain n x| ≤
      ch6Entry14_coarseRemainderBound n x := by
    apply le_of_tendsto'
      ((ch6Entry14_tendsto_emRemainder_atTop x n hx hn hs).abs)
    intro J
    exact ch6Entry14_abs_emRemainder_le n J x hn hx
  calc
    |chapter6Entry14MinusSum x - ch6Entry14_minusMain n x| ≤
        ch6Entry14_coarseRemainderBound n x := hcoarse
    _ ≤ |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
        x ^ (2 * n) / ((2 * n).factorial : ℝ) * (Real.pi ^ 2 / 6) :=
      ch6Entry14_coarseRemainderBound_le_frozen n x hn
    _ ≤ |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
        x ^ (2 * n) / ((2 * n).factorial : ℝ) *
          (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6) := by
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (by positivity)) (by positivity)

/-- **Summability of the Lambert series $\sum_k 1/(e^{kx}-1)$.** For every real $x > 0$, the
series $\sum_{k=1}^{\infty} \frac{1}{e^{kx} - 1}$ is summable. -/
theorem summable_chapter6Entry14MinusTerm (x : ℝ) (hx : 0 < x) :
    Summable (chapter6Entry14MinusTerm x) :=
  ch6Entry14_minusTerm_summable x hx

/-- **Remainder bound for the Lambert series $\sum_k 1/(e^{kx}-1)$.** Let $x > 0$ be real and
let $n \ge 1$ be an integer. Let $S(x) = \sum_{k=1}^{\infty} \frac{1}{e^{kx} - 1}$, let $B_m$ be
the $m$-th Bernoulli number, let $\gamma$ be the Euler–Mascheroni constant, and let
$C_n(x) = \sum_{k=1}^{n} \frac{B_{2k}^2 \, x^{2k-1}}{2k \, (2k)!}$. Then
$\left| S(x) - \left( \frac{\gamma}{x} - \frac{\log x}{x} + \frac14 - C_n(x) \right) \right|
\le \frac{|B_{2n} B_{2n+2}| \, x^{2n}}{(2n)!}
\left( \frac{x^2}{4\pi^2} + \frac{\pi^2}{6} \right)$. -/
theorem chapter6Entry14MinusSum_error_le (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n) :
    |chapter6Entry14MinusSum x -
        (Real.eulerMascheroniConstant / x - Real.log x / x + 1 / 4 -
          chapter6Entry14MinusCorrection n x)| ≤
      |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
        x ^ (2 * n) / ((2 * n).factorial : ℝ) *
        (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6) := by
  simpa [ch6Entry14_minusMain] using
    ch6Entry14_minus_asymptotic_bound x n hx hn
      (summable_chapter6Entry14MinusTerm x hx)


/-- **Asymptotic expansion of the Lambert series $\sum_k 1/(e^{kx}-1)$.** Let $x > 0$ be real
and let $n \ge 1$ be an integer. Let $B_m$ be the $m$-th Bernoulli number, let $\gamma$ be the
Euler–Mascheroni constant, and let
$C_n(x) = \sum_{k=1}^{n} \frac{B_{2k}^2 \, x^{2k-1}}{2k \, (2k)!}$. Then the series
$\sum_{k=1}^{\infty} \frac{1}{e^{kx} - 1}$ is summable, and its sum $S(x)$ satisfies
$\left| S(x) - \left( \frac{\gamma}{x} - \frac{\log x}{x} + \frac14 - C_n(x) \right) \right|
\le \frac{|B_{2n} B_{2n+2}| \, x^{2n}}{(2n)!} \left( \frac{x^2}{4\pi^2} + \frac{\pi^2}{6} \right)$.

The proof applies the Euler–Maclaurin formula to the smooth Mittag-Leffler kernel and bounds
the periodic Bernoulli remainder by its Fourier series.

Proves `Wanted` entry `ramanujan_part1_ch6_entry10_centralbinomialfull`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
-/
theorem ramanujan_part1_ch6_entry10_centralbinomialfull (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n) :
    Summable (chapter6Entry14MinusTerm x) ∧
      |chapter6Entry14MinusSum x -
          (Real.eulerMascheroniConstant / x - Real.log x / x + 1 / 4 -
            chapter6Entry14MinusCorrection n x)| ≤
        |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
          x ^ (2 * n) / ((2 * n).factorial : ℝ) *
          (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6) := by
  exact ⟨summable_chapter6Entry14MinusTerm x hx,
    chapter6Entry14MinusSum_error_le x n hx hn⟩

end

end Entry10Centralbinomialfull

namespace Entry10Centralbinomialexpansion

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry10Centralbinomialfull

noncomputable section

private noncomputable def ch6Entry14_minusMain (n : ℕ) (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant / x - Real.log x / x + 1 / 4 -
    chapter6Entry14MinusCorrection n x

private lemma ch6Entry14_plusTerm_eq_minusTerm_sub (x : ℝ) (hx : 0 < x) (j : ℕ) :
    chapter6Entry14PlusTerm x j =
      chapter6Entry14MinusTerm x j - 2 * chapter6Entry14MinusTerm (2 * x) j := by
  let u : ℝ := ((j + 1 : ℕ) : ℝ) * x
  have hu : 0 < u := by
    unfold u
    positivity
  have hE : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have hE1 : Real.exp u - 1 ≠ 0 := sub_ne_zero.mpr hE.ne'
  have hEp1 : Real.exp u + 1 ≠ 0 := by positivity
  have hE2 : Real.exp u ^ 2 - 1 ≠ 0 := by nlinarith
  unfold chapter6Entry14PlusTerm chapter6Entry14MinusTerm
  change 1 / (Real.exp u + 1) =
    1 / (Real.exp u - 1) -
      2 * (1 / (Real.exp (((j + 1 : ℕ) : ℝ) * (2 * x)) - 1))
  have hscale : ((j + 1 : ℕ) : ℝ) * (2 * x) = u + u := by
    unfold u
    ring
  rw [hscale, Real.exp_add]
  field_simp [hE1, hEp1, hE2]
  ring

private lemma ch6Entry14_plusCorrection_eq (n : ℕ) (x : ℝ) :
    chapter6Entry14PlusCorrection n x =
      2 * chapter6Entry14MinusCorrection n (2 * x) -
        chapter6Entry14MinusCorrection n x := by
  unfold chapter6Entry14PlusCorrection chapter6Entry14MinusCorrection
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [mul_pow]
  have he : 2 * (j + 1) = (2 * (j + 1) - 1) + 1 := by omega
  have hp : (2 : ℝ) ^ (2 * (j + 1)) =
      (2 : ℝ) ^ (2 * (j + 1) - 1) * 2 := by
    exact (congr_arg (fun q : ℕ ↦ (2 : ℝ) ^ q) he).trans (pow_succ _ _)
  rw [hp]
  ring

private lemma ch6Entry14_plusSummable_and_sum_eq (x : ℝ) (hx : 0 < x)
    (hs₁ : Summable (chapter6Entry14MinusTerm x))
    (hs₂ : Summable (chapter6Entry14MinusTerm (2 * x))) :
    Summable (chapter6Entry14PlusTerm x) ∧
      chapter6Entry14PlusSum x = chapter6Entry14MinusSum x -
        2 * chapter6Entry14MinusSum (2 * x) := by
  have hsSub := hs₁.sub (hs₂.mul_left 2)
  have hplus : Summable (chapter6Entry14PlusTerm x) :=
    hsSub.congr fun j ↦ (ch6Entry14_plusTerm_eq_minusTerm_sub x hx j).symm
  refine ⟨hplus, ?_⟩
  unfold chapter6Entry14PlusSum chapter6Entry14MinusSum
  rw [tsum_congr (ch6Entry14_plusTerm_eq_minusTerm_sub x hx),
    hs₁.tsum_sub (hs₂.mul_left 2), tsum_mul_left]

/-- **Summability of the Lambert series $\sum_k 1/(e^{kx}+1)$.** For every real $x > 0$, the
series $\sum_{k=1}^{\infty} \frac{1}{e^{kx} + 1}$ is summable. -/
theorem summable_chapter6Entry14PlusTerm (x : ℝ) (hx : 0 < x) :
    Summable (chapter6Entry14PlusTerm x) := by
  exact (ch6Entry14_plusSummable_and_sum_eq x hx
    (summable_chapter6Entry14MinusTerm x hx)
    (summable_chapter6Entry14MinusTerm (2 * x) (by positivity))).1

private lemma ch6Entry14_plus_error_eq (x : ℝ) (n : ℕ) (hx : 0 < x)
    (hs₁ : Summable (chapter6Entry14MinusTerm x))
    (hs₂ : Summable (chapter6Entry14MinusTerm (2 * x))) :
    chapter6Entry14PlusSum x -
        (Real.log 2 / x - 1 / 4 + chapter6Entry14PlusCorrection n x) =
      (chapter6Entry14MinusSum x - ch6Entry14_minusMain n x) -
        2 * (chapter6Entry14MinusSum (2 * x) - ch6Entry14_minusMain n (2 * x)) := by
  rw [(ch6Entry14_plusSummable_and_sum_eq x hx hs₁ hs₂).2,
    ch6Entry14_plusCorrection_eq]
  unfold ch6Entry14_minusMain
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne']
  field_simp [hx.ne']
  ring

private lemma ch6Entry14_plus_asymptotic_bound (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n)
    (hs₁ : Summable (chapter6Entry14MinusTerm x))
    (hs₂ : Summable (chapter6Entry14MinusTerm (2 * x))) :
    |chapter6Entry14PlusSum x -
        (Real.log 2 / x - 1 / 4 + chapter6Entry14PlusCorrection n x)| ≤
      |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
        x ^ (2 * n) / ((2 * n).factorial : ℝ) *
        (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6 +
          (2 : ℝ) ^ (2 * n + 1) *
            (x ^ 2 / Real.pi ^ 2 + Real.pi ^ 2 / 6)) := by
  let e₁ := chapter6Entry14MinusSum x - ch6Entry14_minusMain n x
  let e₂ := chapter6Entry14MinusSum (2 * x) - ch6Entry14_minusMain n (2 * x)
  have h₁ := chapter6Entry14MinusSum_error_le x n hx hn
  have h₂ := chapter6Entry14MinusSum_error_le (2 * x) n (by positivity) hn
  rw [ch6Entry14_plus_error_eq x n hx hs₁ hs₂]
  change |e₁ - 2 * e₂| ≤ _
  calc
    |e₁ - 2 * e₂| ≤ |e₁| + |2 * e₂| := abs_sub _ _
    _ = |e₁| + 2 * |e₂| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤
        (|(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
          x ^ (2 * n) / ((2 * n).factorial : ℝ) *
            (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6)) +
        2 * (|(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
          (2 * x) ^ (2 * n) / ((2 * n).factorial : ℝ) *
            ((2 * x) ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6)) := by
      exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num))
    _ = _ := by
      rw [mul_pow, mul_pow]
      have hp : (2 : ℝ) * 2 ^ (2 * n) = 2 ^ (2 * n + 1) := by
        rw [pow_succ]
        ring
      rw [← hp]
      norm_num [pow_two]
      ring

/-- **Asymptotic expansion of the Lambert series $\sum_k 1/(e^{kx}+1)$.** Let $x > 0$ be real
and let $n \ge 1$ be an integer. Let $B_m$ be the $m$-th Bernoulli number and let
$D_n(x) = \sum_{k=1}^{n} \frac{(2^{2k} - 1) \, B_{2k}^2 \, x^{2k-1}}{2k \, (2k)!}$. Then the
series $\sum_{k=1}^{\infty} \frac{1}{e^{kx} + 1}$ is summable, and its sum $T(x)$ satisfies
$\left| T(x) - \left( \frac{\log 2}{x} - \frac14 + D_n(x) \right) \right|
\le \frac{|B_{2n} B_{2n+2}| \, x^{2n}}{(2n)!} \left( \frac{x^2}{4\pi^2} + \frac{\pi^2}{6} +
2^{2n+1} \left( \frac{x^2}{\pi^2} + \frac{\pi^2}{6} \right) \right)$.

The proof writes this series as the series $\sum_k 1/(e^{kx}-1)$ minus twice the same series
at $2x$, and applies the remainder bound for $\sum_k 1/(e^{kx}-1)$.

Proves `Wanted` entry `ramanujan_part1_ch6_entry10_centralbinomialexpansion`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
-/
theorem ramanujan_part1_ch6_entry10_centralbinomialexpansion (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n) :
    Summable (chapter6Entry14PlusTerm x) ∧
      |chapter6Entry14PlusSum x -
          (Real.log 2 / x - 1 / 4 + chapter6Entry14PlusCorrection n x)| ≤
        |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
          x ^ (2 * n) / ((2 * n).factorial : ℝ) *
          (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6 +
            (2 : ℝ) ^ (2 * n + 1) *
              (x ^ 2 / Real.pi ^ 2 + Real.pi ^ 2 / 6)) := by
  have hs₁ := summable_chapter6Entry14MinusTerm x hx
  have hs₂ := summable_chapter6Entry14MinusTerm (2 * x) (by positivity)
  exact ⟨(ch6Entry14_plusSummable_and_sum_eq x hx hs₁ hs₂).1,
    ch6Entry14_plus_asymptotic_bound x n hx hn hs₁ hs₂⟩

end

end Entry10Centralbinomialexpansion

end MathlibExt.Analysis.Ramanujan.Part1Ch6
