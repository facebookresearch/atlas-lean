/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry12SummableSuccN
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry16Corollary1JensenSeries

/-!
# Ramanujan's psi-series identity

This file proves Berndt's formulas (16.4)-(16.5) for Ramanujan's recursively defined
psi-polynomials and their associated exponential series.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry16PsiSeries

def psi : ℕ → ℕ → ℂ → ℂ
  | 0, 1, _ => 1
  | 0, _, _ => 0
  | r + 1, k, n =>
      (n - (↑(r + 1) : ℂ) - (↑k : ℂ) + 1) * psi r k n +
        ((↑(r + 1) : ℂ) + (↑k : ℂ) - 2) * if k = 0 then 0 else psi r (k - 1) n

private noncomputable def e16ps_term (r : ℕ) (n u : ℂ) (j : ℕ) : ℂ :=
  (n + (j : ℂ)) ^ (r + j) * Complex.exp (-u * (n + (j : ℂ))) * u ^ j /
    (Nat.factorial j : ℂ)

private noncomputable def e16ps_G (r : ℕ) (n u : ℂ) : ℂ :=
  ∑' j : ℕ, e16ps_term r n u j

private noncomputable def e16ps_P (r : ℕ) (n u : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (r + 1), psi r k n / (1 - u) ^ (r + k)

private def e16ps_D : Set ℂ :=
  {u | ‖u * Complex.exp (1 - u)‖ < 1 ∧ ‖u‖ < 1}

private noncomputable def e16ps_q (u : ℂ) : ℝ :=
  ‖u * Complex.exp (-u)‖

private lemma e16ps_psi_zero (r : ℕ) (n : ℂ) : psi r 0 n = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp [psi, ih]

private lemma e16ps_psi_eq_zero_of_lt (r k : ℕ) (n : ℂ) (h : r + 1 < k) :
    psi r k n = 0 := by
  induction r generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ r ih =>
    have h₁ : psi r k n = 0 := ih k (by omega)
    have hk : k ≠ 0 := by omega
    have h₂ : psi r (k - 1) n = 0 := ih (k - 1) (by omega)
    simp [psi, h₁, h₂, hk]

private lemma e16ps_norm_eq_exp_mul_q (u : ℂ) :
    ‖u * Complex.exp (1 - u)‖ = Real.exp 1 * e16ps_q u := by
  have harg : (1 - u : ℂ) = 1 + -u := by ring
  rw [harg, Complex.exp_add, norm_mul, norm_mul, Complex.norm_exp]
  simp [e16ps_q, mul_comm]
  ring

private lemma e16ps_q_lt_exp_neg_one {u : ℂ}
    (h : ‖u * Complex.exp (1 - u)‖ < 1) :
    e16ps_q u < Real.exp (-1) := by
  rw [e16ps_norm_eq_exp_mul_q] at h
  rw [Real.exp_neg, inv_eq_one_div, lt_div_iff₀ (Real.exp_pos 1)]
  simpa [mul_comm] using h

private lemma e16ps_term_eq_entry12 (r j : ℕ) (n u : ℂ) :
    e16ps_term r n u j = Complex.exp (-u * n) *
      ((n + (j : ℂ)) ^ (r + j) /
        ((Complex.exp u / u) ^ j * (Nat.factorial j : ℂ))) := by
  have hexp : Complex.exp (-u * (n + (j : ℂ))) =
      Complex.exp (-u * n) * Complex.exp (-u) ^ j := by
    rw [show -u * (n + (j : ℂ)) = -u * n + (j : ℂ) * (-u) by ring,
      Complex.exp_add, Complex.exp_nat_mul]
  have hinv : (Complex.exp u / u)⁻¹ = u * Complex.exp (-u) := by
    rw [inv_div, Complex.exp_neg, div_eq_mul_inv]
  have hpow : Complex.exp (-u) ^ j * u ^ j =
      (u * Complex.exp (-u)) ^ j := by
    rw [mul_pow]
    ring
  unfold e16ps_term
  rw [hexp]
  calc
    (n + (j : ℂ)) ^ (r + j) *
          (Complex.exp (-u * n) * Complex.exp (-u) ^ j) * u ^ j /
        (Nat.factorial j : ℂ) =
        Complex.exp (-u * n) * ((n + (j : ℂ)) ^ (r + j) *
          (Complex.exp (-u) ^ j * u ^ j) / (Nat.factorial j : ℂ)) := by ring
    _ = Complex.exp (-u * n) * ((n + (j : ℂ)) ^ (r + j) *
          ((Complex.exp u / u) ^ j)⁻¹ / (Nat.factorial j : ℂ)) := by
      rw [hpow, ← hinv, inv_pow]
    _ = Complex.exp (-u * n) *
          ((n + (j : ℂ)) ^ (r + j) /
            ((Complex.exp u / u) ^ j * (Nat.factorial j : ℂ))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private lemma e16ps_norm_exp_div (u : ℂ) (hu : u ≠ 0) :
    ‖Complex.exp u / u‖ = 1 / e16ps_q u := by
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  unfold e16ps_q
  rw [norm_div, norm_mul, Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.neg_re, Real.exp_neg]
  field_simp

private lemma e16ps_summable_norm (r : ℕ) (n u : ℂ)
    (h : ‖u * Complex.exp (1 - u)‖ < 1) :
    Summable (fun j : ℕ => ‖e16ps_term r n u j‖) := by
  by_cases hu : u = 0
  · subst u
    apply summable_of_ne_finset_zero (s := {0})
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [e16ps_term, hj]
  · have hqpos : 0 < e16ps_q u := by
      apply norm_pos_iff.mpr
      exact mul_ne_zero hu (Complex.exp_ne_zero _)
    have ha : Real.exp 1 < ‖Complex.exp u / u‖ := by
      rw [e16ps_norm_exp_div u hu]
      have hinv := one_div_lt_one_div_of_lt hqpos (e16ps_q_lt_exp_neg_one h)
      simpa [Real.exp_neg] using hinv
    have hs :=
      Entry12SummableSuccN.ramanujan_part1_ch3_entry12_summable_succ_n_general
        ((r : ℤ) - 1) n (Complex.exp u / u) (Or.inl ha)
    have hs' : Summable (fun j : ℕ =>
        ‖(n + (j : ℂ)) ^ (r + j) /
          ((Complex.exp u / u) ^ j * (Nat.factorial j : ℂ))‖) := by
      apply hs.congr
      intro j
      rw [show (r : ℤ) - 1 + 1 + (j : ℤ) = ((r + j : ℕ) : ℤ) by omega,
        zpow_natCast]
    apply (hs'.mul_left ‖Complex.exp (-u * n)‖).congr
    intro j
    rw [e16ps_term_eq_entry12, norm_mul]

private lemma e16ps_term_eq_qform (r j : ℕ) (n w : ℂ) :
    e16ps_term r n w j = Complex.exp (-w * n) *
      ((n + (j : ℂ)) ^ (r + j) * (w * Complex.exp (-w)) ^ j /
        (Nat.factorial j : ℂ)) := by
  have hexp : Complex.exp (-w * (n + (j : ℂ))) =
      Complex.exp (-w * n) * Complex.exp (-w) ^ j := by
    rw [show -w * (n + (j : ℂ)) = -w * n + (j : ℂ) * (-w) by ring,
      Complex.exp_add, Complex.exp_nat_mul]
  unfold e16ps_term
  rw [hexp, mul_pow]
  ring

private lemma e16ps_entry_norm_eq (r j : ℕ) (n : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    ‖(n + (j : ℂ)) ^ (r + j) /
        (((ρ⁻¹ : ℝ) : ℂ) ^ j * (Nat.factorial j : ℂ))‖ =
      ‖n + (j : ℂ)‖ ^ (r + j) * ρ ^ j / (Nat.factorial j : ℝ) := by
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), Complex.norm_natCast, inv_pow]
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hfac : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  field_simp

private lemma e16ps_majorant_summable (r : ℕ) (n : ℂ) (ρ B : ℝ)
    (hρpos : 0 < ρ) (hρ : ρ < Real.exp (-1)) :
    Summable (fun j : ℕ => Real.exp (B * ‖n‖) *
      (‖n + (j : ℂ)‖ ^ (r + j) * ρ ^ j / (Nat.factorial j : ℝ))) := by
  have hinv : Real.exp 1 < ρ⁻¹ := by
    have h := one_div_lt_one_div_of_lt hρpos hρ
    simpa [Real.exp_neg] using h
  have ha : Real.exp 1 < ‖((ρ⁻¹ : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρpos)]
    exact hinv
  have hs :=
    Entry12SummableSuccN.ramanujan_part1_ch3_entry12_summable_succ_n_general
      ((r : ℤ) - 1) n ((ρ⁻¹ : ℝ) : ℂ) (Or.inl ha)
  have hs' : Summable (fun j : ℕ =>
      ‖n + (j : ℂ)‖ ^ (r + j) * ρ ^ j / (Nat.factorial j : ℝ)) := by
    apply hs.congr
    intro j
    rw [show (r : ℤ) - 1 + 1 + (j : ℤ) = ((r + j : ℕ) : ℤ) by omega,
      zpow_natCast, e16ps_entry_norm_eq r j n ρ hρpos]
  exact hs'.mul_left _

private lemma e16ps_term_norm_le_majorant (r j : ℕ) (n w : ℂ) (ρ B : ℝ)
    (hw : ‖w‖ ≤ B) (hq : e16ps_q w ≤ ρ) :
    ‖e16ps_term r n w j‖ ≤ Real.exp (B * ‖n‖) *
      (‖n + (j : ℂ)‖ ^ (r + j) * ρ ^ j / (Nat.factorial j : ℝ)) := by
  have hre : (-w * n).re ≤ B * ‖n‖ := by
    calc
      (-w * n).re ≤ ‖-w * n‖ := Complex.re_le_norm _
      _ ≤ ‖-w‖ * ‖n‖ := norm_mul_le _ _
      _ = ‖w‖ * ‖n‖ := by rw [norm_neg]
      _ ≤ B * ‖n‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg n)
  have hexp : ‖Complex.exp (-w * n)‖ ≤ Real.exp (B * ‖n‖) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hre
  have hpow : e16ps_q w ^ j ≤ ρ ^ j :=
    pow_le_pow_left₀ (norm_nonneg _) hq j
  have hinner :
      ‖n + (j : ℂ)‖ ^ (r + j) * e16ps_q w ^ j / (Nat.factorial j : ℝ) ≤
        ‖n + (j : ℂ)‖ ^ (r + j) * ρ ^ j / (Nat.factorial j : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left hpow (pow_nonneg (norm_nonneg _) _)
  rw [e16ps_term_eq_qform, norm_mul, norm_div, norm_mul, norm_pow,
    norm_pow, Complex.norm_natCast]
  change ‖Complex.exp (-w * n)‖ *
      (‖n + (j : ℂ)‖ ^ (r + j) * e16ps_q w ^ j / (Nat.factorial j : ℝ)) ≤ _
  calc
    _ ≤ Real.exp (B * ‖n‖) *
        (‖n + (j : ℂ)‖ ^ (r + j) * e16ps_q w ^ j /
          (Nat.factorial j : ℝ)) :=
      mul_le_mul_of_nonneg_right hexp <|
        div_nonneg
          (mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _))
          (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le

private lemma e16ps_local_bound (r : ℕ) (n u : ℂ)
    (h : ‖u * Complex.exp (1 - u)‖ < 1) :
    ∃ (U : Set ℂ) (b : ℕ → ℝ), IsOpen U ∧ u ∈ U ∧ Summable b ∧
      ∀ (j : ℕ) (w : ℂ), w ∈ U → ‖e16ps_term r n w j‖ ≤ b j := by
  obtain ⟨ρ, huρ, hρ⟩ := exists_between (e16ps_q_lt_exp_neg_one h)
  have hρpos : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) huρ
  let U : Set ℂ := {w | e16ps_q w < ρ} ∩ Metric.ball u 1
  let b : ℕ → ℝ := fun j => Real.exp ((‖u‖ + 1) * ‖n‖) *
    (‖n + (j : ℂ)‖ ^ (r + j) * ρ ^ j / (Nat.factorial j : ℝ))
  have hqcont : Continuous e16ps_q := by
    unfold e16ps_q
    exact (continuous_id.mul (Complex.continuous_exp.comp continuous_neg)).norm
  have hUopen : IsOpen U :=
    (isOpen_lt hqcont continuous_const).inter Metric.isOpen_ball
  have huU : u ∈ U := by
    refine ⟨huρ, ?_⟩
    simp
  have hb : Summable b :=
    e16ps_majorant_summable r n ρ (‖u‖ + 1) hρpos hρ
  refine ⟨U, b, hUopen, huU, hb, ?_⟩
  intro j w hw
  have hdist : dist w u < 1 := hw.2
  have hwnorm : ‖w‖ ≤ ‖u‖ + 1 := by
    apply le_of_lt
    calc
      ‖w‖ = ‖(w - u) + u‖ := by ring_nf
      _ ≤ ‖w - u‖ + ‖u‖ := norm_add_le _ _
      _ < 1 + ‖u‖ := by
        rw [dist_eq_norm] at hdist
        linarith
      _ = ‖u‖ + 1 := by ring
  exact e16ps_term_norm_le_majorant r j n w ρ (‖u‖ + 1) hwnorm hw.1.le

private lemma e16ps_term_differentiable (r j : ℕ) (n : ℂ) :
    Differentiable ℂ (fun u : ℂ => e16ps_term r n u j) := by
  unfold e16ps_term
  fun_prop

private lemma e16ps_differentiableAt_G (r : ℕ) (n u : ℂ)
    (h : ‖u * Complex.exp (1 - u)‖ < 1) :
    DifferentiableAt ℂ (e16ps_G r n) u := by
  obtain ⟨U, b, hUopen, huU, hb, hbound⟩ := e16ps_local_bound r n u h
  have hd : DifferentiableOn ℂ (e16ps_G r n) U := by
    unfold e16ps_G
    exact Complex.differentiableOn_tsum_of_summable_norm hb
      (fun j => (e16ps_term_differentiable r j n).differentiableOn) hUopen hbound
  exact hd.differentiableAt (hUopen.mem_nhds huU)

private lemma e16ps_hasSum_deriv (r : ℕ) (n u : ℂ)
    (h : ‖u * Complex.exp (1 - u)‖ < 1) :
    HasSum (fun j : ℕ => deriv (fun w : ℂ => e16ps_term r n w j) u)
      (deriv (e16ps_G r n) u) := by
  obtain ⟨U, b, hUopen, huU, hb, hbound⟩ := e16ps_local_bound r n u h
  unfold e16ps_G
  exact Complex.hasSum_deriv_of_summable_norm hb
    (fun j => (e16ps_term_differentiable r j n).differentiableOn)
    hUopen hbound huU

private lemma e16ps_term_recurrence (r j : ℕ) (n u : ℂ) :
    (1 - u) * e16ps_term (r + 1) n u j =
      n * e16ps_term r n u j +
        u * deriv (fun w : ℂ => e16ps_term r n w j) u := by
  have hlin : HasDerivAt (fun w : ℂ => -w * (n + (j : ℂ)))
      (-(n + (j : ℂ))) u := by
    simpa using (hasDerivAt_id u).neg.mul_const (n + (j : ℂ))
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (-w * (n + (j : ℂ))))
      (Complex.exp (-u * (n + (j : ℂ))) * (-(n + (j : ℂ)))) u :=
    (Complex.hasDerivAt_exp _).comp u hlin
  have hpow : HasDerivAt (fun w : ℂ => w ^ j)
      ((j : ℂ) * u ^ (j - 1)) u := by
    simpa using (hasDerivAt_id u).fun_pow j
  have hraw := ((hexp.mul hpow).const_mul ((n + (j : ℂ)) ^ (r + j))).div_const
    (Nat.factorial j : ℂ)
  have hderiv : HasDerivAt (fun w : ℂ => e16ps_term r n w j)
      ((n + (j : ℂ)) ^ (r + j) * Complex.exp (-u * (n + (j : ℂ))) *
          ((j : ℂ) * u ^ (j - 1) - (n + (j : ℂ)) * u ^ j) /
        (Nat.factorial j : ℂ)) u := by
    convert hraw using 1
    · funext w
      unfold e16ps_term
      dsimp
      ring
    · ring
  rw [hderiv.deriv]
  unfold e16ps_term
  cases j with
  | zero =>
    simp only [Nat.cast_zero, add_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, zero_mul, zero_sub]
    rw [show r + 1 = (r + 0) + 1 by omega, pow_succ]
    ring
  | succ j =>
    simp only [Nat.cast_succ, Nat.succ_sub_one]
    rw [show r + 1 + (j + 1) = (r + (j + 1)) + 1 by omega, pow_succ,
      pow_succ u j]
    ring

private lemma e16ps_G_recurrence (r : ℕ) (n u : ℂ)
    (h : ‖u * Complex.exp (1 - u)‖ < 1) :
    (1 - u) * e16ps_G (r + 1) n u =
      n * e16ps_G r n u + u * deriv (e16ps_G r n) u := by
  have hGr : HasSum (fun j : ℕ => e16ps_term r n u j) (e16ps_G r n u) := by
    unfold e16ps_G
    exact (e16ps_summable_norm r n u h).of_norm.hasSum
  have hGs : HasSum (fun j : ℕ => e16ps_term (r + 1) n u j)
      (e16ps_G (r + 1) n u) := by
    unfold e16ps_G
    exact (e16ps_summable_norm (r + 1) n u h).of_norm.hasSum
  have hd := e16ps_hasSum_deriv r n u h
  have hright := (hGr.mul_left n).add (hd.mul_left u)
  have hleft' : HasSum (fun j : ℕ => (1 - u) * e16ps_term (r + 1) n u j)
      (n * e16ps_G r n u + u * deriv (e16ps_G r n) u) :=
    hright.congr_fun fun j => e16ps_term_recurrence r j n u
  exact (hGs.mul_left (1 - u)).unique hleft'

private lemma e16ps_isOpen_D : IsOpen e16ps_D := by
  have hfirst : Continuous (fun u : ℂ => ‖u * Complex.exp (1 - u)‖) :=
    (continuous_id.mul
      (Complex.continuous_exp.comp (continuous_const.sub continuous_id))).norm
  have hsecond : Continuous (fun u : ℂ => ‖u‖) := continuous_norm
  exact (isOpen_lt hfirst continuous_const).inter (isOpen_lt hsecond continuous_const)

private lemma e16ps_differentiableOn_G (r : ℕ) (n : ℂ) :
    DifferentiableOn ℂ (e16ps_G r n) e16ps_D := by
  intro u hu
  exact (e16ps_differentiableAt_G r n u hu.1).differentiableWithinAt

private lemma e16ps_analyticOnNhd_G (r : ℕ) (n : ℂ) :
    AnalyticOnNhd ℂ (e16ps_G r n) e16ps_D :=
  (e16ps_differentiableOn_G r n).analyticOnNhd e16ps_isOpen_D

private lemma e16ps_scale_exp_le_one (a t : ℝ) (ha : a < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * Real.exp ((1 - t) * a) ≤ 1 := by
  by_cases ht : t = 0
  · simp [ht]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hmul : (1 - t) * a ≤ (1 - t) * 1 :=
      mul_le_mul_of_nonneg_left ha.le (sub_nonneg.mpr ht1)
    have hlog : Real.log t + (1 - t) * a ≤ 0 := by
      linarith [Real.log_le_sub_one_of_pos htpos]
    calc
      t * Real.exp ((1 - t) * a) =
          Real.exp (Real.log t + (1 - t) * a) := by
        rw [Real.exp_add, Real.exp_log htpos]
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hlog
      _ = 1 := Real.exp_zero

private lemma e16ps_q_smul_le (u : ℂ) (hu : ‖u‖ < 1) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    e16ps_q (t • u) ≤ e16ps_q u := by
  have hre : u.re < 1 := lt_of_le_of_lt (Complex.re_le_norm u) hu
  have hfactor := e16ps_scale_exp_le_one u.re t hre ht0 ht1
  have hexp : Real.exp (-(t * u.re)) =
      Real.exp (-u.re) * Real.exp ((1 - t) * u.re) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscale : e16ps_q (t • u) =
      t * ‖u‖ * Real.exp (-(t * u.re)) := by
    simp [e16ps_q, Complex.norm_exp, Real.norm_eq_abs,
      abs_of_nonneg ht0]
  have hbase : e16ps_q u = ‖u‖ * Real.exp (-u.re) := by
    simp [e16ps_q, Complex.norm_exp]
  rw [hscale, hbase, hexp]
  calc
    t * ‖u‖ * (Real.exp (-u.re) * Real.exp ((1 - t) * u.re)) =
        (‖u‖ * Real.exp (-u.re)) *
          (t * Real.exp ((1 - t) * u.re)) := by ring
    _ ≤ (‖u‖ * Real.exp (-u.re)) * 1 :=
      mul_le_mul_of_nonneg_left hfactor
        (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    _ = ‖u‖ * Real.exp (-u.re) := by ring

private lemma e16ps_zero_mem_D : (0 : ℂ) ∈ e16ps_D := by
  simp [e16ps_D]

private lemma e16ps_starConvex_D : StarConvex ℝ (0 : ℂ) e16ps_D := by
  intro u hu a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  simp only [smul_zero, zero_add]
  constructor
  · rw [e16ps_norm_eq_exp_mul_q]
    calc
      Real.exp 1 * e16ps_q (b • u) ≤ Real.exp 1 * e16ps_q u :=
        mul_le_mul_of_nonneg_left (e16ps_q_smul_le u hu.2 b hb hb1)
          (Real.exp_pos _).le
      _ = ‖u * Complex.exp (1 - u)‖ := (e16ps_norm_eq_exp_mul_q u).symm
      _ < 1 := hu.1
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    calc
      b * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
      _ < 1 := by simpa using hu.2

private lemma e16ps_isPreconnected_D : IsPreconnected e16ps_D :=
  (e16ps_starConvex_D.isPathConnected e16ps_zero_mem_D).isConnected.isPreconnected

private lemma e16ps_exists_jensen_radius :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ * Real.exp (ρ + 1) = 1 := by
  let f : ℝ → ℝ := fun x => x * Real.exp (x + 1)
  have hf : Continuous f := continuous_id.mul <|
    Real.continuous_exp.comp (continuous_id.add continuous_const)
  have hmem : (1 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
    constructor
    · simp [f]
    · simp only [f, one_mul]
      exact (Real.one_lt_exp_iff.mpr (by norm_num)).le
  obtain ⟨ρ, hρmem, hρeq⟩ :=
    (intermediate_value_Icc (a := (0 : ℝ)) (b := 1) zero_le_one hf.continuousOn) hmem
  have hρne : ρ ≠ 0 := by
    intro hρ
    subst ρ
    simp [f] at hρeq
  exact ⟨ρ, lt_of_le_of_ne hρmem.1 (Ne.symm hρne), hρeq⟩

private lemma e16ps_G_zero_ofReal (n : ℂ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hρeq : ρ * Real.exp (ρ + 1) = 1) (t : ℝ) (ht : -ρ < t ∧ t < 1) :
    e16ps_G 0 n (t : ℂ) = 1 / (1 - (t : ℂ)) := by
  let x : ℂ := n * (t : ℂ)
  have hJ :=
    Entry16Corollary1JensenSeries.ramanujan_part1_ch3_entry16_corollary1_jensen_series
      ρ hρpos hρeq t ht x
  have hm := hJ.mul_left (Complex.exp (-x))
  have hterm : ∀ j : ℕ, e16ps_term 0 n (t : ℂ) j =
      Complex.exp (-x) *
        ((x + (j : ℂ) * (t : ℂ)) ^ j /
          ((Nat.factorial j : ℂ) * Complex.exp ((j : ℂ) * (t : ℂ)))) := by
    intro j
    have hbase : x + (j : ℂ) * (t : ℂ) = (n + (j : ℂ)) * (t : ℂ) := by
      simp only [x]
      ring
    have hexp : Complex.exp (-(t : ℂ) * (n + (j : ℂ))) =
        Complex.exp (-x) / Complex.exp ((j : ℂ) * (t : ℂ)) := by
      rw [eq_div_iff (Complex.exp_ne_zero _), ← Complex.exp_add]
      congr 1
      simp only [x]
      ring
    unfold e16ps_term
    simp only [zero_add]
    rw [hbase, mul_pow, hexp]
    field_simp
  have hm' := hm.congr_fun hterm
  have hvalue : Complex.exp (-x) * (Complex.exp x / (1 - (t : ℂ))) =
      1 / (1 - (t : ℂ)) := by
    calc
      Complex.exp (-x) * (Complex.exp x / (1 - (t : ℂ))) =
          (Complex.exp (-x) * Complex.exp x) / (1 - (t : ℂ)) := by ring
      _ = 1 / (1 - (t : ℂ)) := by
        rw [← Complex.exp_add]
        simp
  rw [hvalue] at hm'
  exact hm'.tsum_eq

private lemma e16ps_one_div_differentiableOn :
    DifferentiableOn ℂ (fun u : ℂ => 1 / (1 - u)) e16ps_D := by
  intro u hu
  have hne : (1 - u : ℂ) ≠ 0 := by
    intro hzero
    have hu1 : u = 1 := (sub_eq_zero.mp hzero).symm
    have hunorm : ‖u‖ < 1 := hu.2
    rw [hu1, norm_one] at hunorm
    linarith
  have hden : DifferentiableAt ℂ (fun z : ℂ => 1 - z) u :=
    (differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id
  exact ((differentiableAt_const (c := (1 : ℂ))).div hden hne).differentiableWithinAt

private lemma e16ps_one_div_analyticOnNhd :
    AnalyticOnNhd ℂ (fun u : ℂ => 1 / (1 - u)) e16ps_D :=
  e16ps_one_div_differentiableOn.analyticOnNhd e16ps_isOpen_D

private lemma e16ps_frequently_base (n : ℂ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hρeq : ρ * Real.exp (ρ + 1) = 1) :
    ∃ᶠ u in nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ),
      e16ps_G 0 n u = 1 / (1 - u) := by
  let z : ℕ → ℂ := fun m => ((1 / ((m : ℝ) + 1) : ℝ) : ℂ)
  have hzlim : Filter.Tendsto z Filter.atTop (nhds (0 : ℂ)) := by
    have hreal : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1))
        Filter.atTop (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hzne : ∀ᶠ m : ℕ in Filter.atTop, z m ∈ ({0}ᶜ : Set ℂ) :=
    Filter.Eventually.of_forall fun m => by
      change (((1 / ((m : ℝ) + 1) : ℝ) : ℂ)) ≠ 0
      exact_mod_cast one_div_ne_zero (by positivity : (m : ℝ) + 1 ≠ 0)
  have hzwithin : Filter.Tendsto z Filter.atTop
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzlim, hzne⟩
  rw [Filter.frequently_iff]
  intro U hU
  have hUevent : ∀ᶠ m : ℕ in Filter.atTop, z m ∈ U := hzwithin.eventually hU
  have hmge : ∀ᶠ m : ℕ in Filter.atTop, 1 ≤ m :=
    Filter.eventually_atTop.mpr ⟨1, fun _ hm => hm⟩
  obtain ⟨m, hmU, hm⟩ := (hUevent.and hmge).exists
  refine ⟨z m, hmU, ?_⟩
  have htpos : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have htlt : 1 / ((m : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    have hmpos : (0 : ℝ) < m := by
      exact_mod_cast (show 0 < m from lt_of_lt_of_le Nat.zero_lt_one hm)
    linarith
  exact e16ps_G_zero_ofReal n ρ hρpos hρeq _ ⟨by linarith, htlt⟩

private lemma e16ps_G_zero (n u : ℂ) (hu : u ∈ e16ps_D) :
    e16ps_G 0 n u = 1 / (1 - u) := by
  obtain ⟨ρ, hρpos, hρeq⟩ := e16ps_exists_jensen_radius
  exact (e16ps_analyticOnNhd_G 0 n).eqOn_of_preconnected_of_frequently_eq
    e16ps_one_div_analyticOnNhd e16ps_isPreconnected_D e16ps_zero_mem_D
      (e16ps_frequently_base n ρ hρpos hρeq) hu

private lemma e16ps_P_zero (n u : ℂ) :
    e16ps_P 0 n u = 1 / (1 - u) := by
  simp [e16ps_P, psi]

private lemma e16ps_hasDerivAt_P_term (c u : ℂ) (m : ℕ) (hu : 1 - u ≠ 0) :
    HasDerivAt (fun w : ℂ => c / (1 - w) ^ m)
      (c * (m : ℂ) / (1 - u) ^ (m + 1)) u := by
  have hbase : HasDerivAt (fun w : ℂ => 1 - w) (-1) u :=
    by
      convert (hasDerivAt_const u (1 : ℂ)).sub (hasDerivAt_id u) using 1
      · funext w
        rfl
      · ring
  have hpow := hbase.fun_pow m
  have hraw := (hasDerivAt_const u c).div hpow (pow_ne_zero m hu)
  convert hraw using 1
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.cast_succ, Nat.succ_sub_one]
    field_simp
    ring

private lemma e16ps_hasDerivAt_P (r : ℕ) (n u : ℂ) (hu : 1 - u ≠ 0) :
    HasDerivAt (e16ps_P r n)
      (∑ k ∈ Finset.Icc 1 (r + 1),
        psi r k n * ((r + k : ℕ) : ℂ) / (1 - u) ^ (r + k + 1)) u := by
  unfold e16ps_P
  exact HasDerivAt.fun_sum fun k _ =>
    e16ps_hasDerivAt_P_term (psi r k n) u (r + k) hu

private lemma e16ps_deriv_P (r : ℕ) (n u : ℂ) (hu : 1 - u ≠ 0) :
    deriv (e16ps_P r n) u =
      ∑ k ∈ Finset.Icc 1 (r + 1),
        psi r k n * ((r + k : ℕ) : ℂ) / (1 - u) ^ (r + k + 1) :=
  (e16ps_hasDerivAt_P r n u hu).deriv

private lemma e16ps_sum_first (r : ℕ) (n v : ℂ) :
    (∑ k ∈ Finset.Icc 1 (r + 2),
        (n - ((r + k : ℕ) : ℂ)) * psi r k n / v ^ (r + k)) =
      ∑ k ∈ Finset.Icc 1 (r + 1),
        (n - ((r + k : ℕ) : ℂ)) * psi r k n / v ^ (r + k) := by
  rw [show r + 2 = (r + 1) + 1 by omega,
    Finset.sum_Icc_succ_top (by omega)]
  rw [e16ps_psi_eq_zero_of_lt r (r + 2) n (by omega)]
  simp

private lemma e16ps_sum_shift (r : ℕ) (n v : ℂ) :
    (∑ k ∈ Finset.Icc 1 (r + 2),
        (((r + k - 1 : ℕ) : ℂ) * psi r (k - 1) n) / v ^ (r + k)) =
      ∑ k ∈ Finset.Icc 1 (r + 1),
        (((r + k : ℕ) : ℂ) * psi r k n) / v ^ (r + k + 1) := by
  have hbij :
      (∑ k ∈ Finset.Icc 1 (r + 1),
          (((r + k : ℕ) : ℂ) * psi r k n) / v ^ (r + k + 1)) =
        ∑ k ∈ Finset.Icc 2 (r + 2),
          (((r + k - 1 : ℕ) : ℂ) * psi r (k - 1) n) / v ^ (r + k) := by
    apply Finset.sum_bij (fun k _ => k + 1)
    · simp only [Finset.mem_Icc]
      omega
    · intro a₁ _ a₂ _ h
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      refine ⟨k - 1, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · omega
    · intro k _
      have hexp : r + (k + 1) = r + k + 1 := by omega
      simp [hexp]
  have hsubset : Finset.Icc 2 (r + 2) ⊆ Finset.Icc 1 (r + 2) :=
    Finset.Icc_subset_Icc (by omega) (by omega)
  have hextend :
      (∑ k ∈ Finset.Icc 2 (r + 2),
          (((r + k - 1 : ℕ) : ℂ) * psi r (k - 1) n) / v ^ (r + k)) =
        ∑ k ∈ Finset.Icc 1 (r + 2),
          (((r + k - 1 : ℕ) : ℂ) * psi r (k - 1) n) / v ^ (r + k) := by
    apply Finset.sum_subset hsubset
    intro k hk hnot
    simp only [Finset.mem_Icc] at hk hnot
    have hk1 : k = 1 := by omega
    subst k
    simp [e16ps_psi_zero]
  exact (hbij.trans hextend).symm

private lemma e16ps_psi_succ (r k : ℕ) (n : ℂ) (hk : 1 ≤ k) :
    psi (r + 1) k n =
      (n - ((r + k : ℕ) : ℂ)) * psi r k n +
        ((r + k - 1 : ℕ) : ℂ) * psi r (k - 1) n := by
  rw [psi]
  split
  · omega
  push_cast [Nat.cast_sub (by omega : 1 ≤ r + k)]
  ring

private lemma e16ps_mul_P_succ (r : ℕ) (n u : ℂ) (hu : 1 - u ≠ 0) :
    (1 - u) * e16ps_P (r + 1) n u =
      (∑ k ∈ Finset.Icc 1 (r + 1),
        (n - ((r + k : ℕ) : ℂ)) * psi r k n / (1 - u) ^ (r + k)) +
      ∑ k ∈ Finset.Icc 1 (r + 1),
        (((r + k : ℕ) : ℂ) * psi r k n) / (1 - u) ^ (r + k + 1) := by
  unfold e16ps_P
  calc
    (1 - u) * (∑ k ∈ Finset.Icc 1 (r + 1 + 1),
        psi (r + 1) k n / (1 - u) ^ (r + 1 + k)) =
        ∑ k ∈ Finset.Icc 1 (r + 2),
          ((n - ((r + k : ℕ) : ℂ)) * psi r k n / (1 - u) ^ (r + k) +
            (((r + k - 1 : ℕ) : ℂ) * psi r (k - 1) n) /
              (1 - u) ^ (r + k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [e16ps_psi_succ r k n hk1]
      rw [show r + 1 + k = (r + k) + 1 by omega, pow_succ]
      field_simp
    _ = (∑ k ∈ Finset.Icc 1 (r + 2),
          (n - ((r + k : ℕ) : ℂ)) * psi r k n / (1 - u) ^ (r + k)) +
        ∑ k ∈ Finset.Icc 1 (r + 2),
          (((r + k - 1 : ℕ) : ℂ) * psi r (k - 1) n) /
            (1 - u) ^ (r + k) := Finset.sum_add_distrib
    _ = _ := by rw [e16ps_sum_first, e16ps_sum_shift]

private lemma e16ps_P_recurrence (r : ℕ) (n u : ℂ) (hu : 1 - u ≠ 0) :
    (1 - u) * e16ps_P (r + 1) n u =
      n * e16ps_P r n u + u * deriv (e16ps_P r n) u := by
  rw [e16ps_mul_P_succ r n u hu, e16ps_deriv_P r n u hu]
  unfold e16ps_P
  calc
    (∑ k ∈ Finset.Icc 1 (r + 1),
        (n - ((r + k : ℕ) : ℂ)) * psi r k n / (1 - u) ^ (r + k)) +
        (∑ k ∈ Finset.Icc 1 (r + 1),
          (((r + k : ℕ) : ℂ) * psi r k n) / (1 - u) ^ (r + k + 1)) =
        ∑ k ∈ Finset.Icc 1 (r + 1),
          ((n - ((r + k : ℕ) : ℂ)) * psi r k n / (1 - u) ^ (r + k) +
            (((r + k : ℕ) : ℂ) * psi r k n) /
              (1 - u) ^ (r + k + 1)) := Finset.sum_add_distrib.symm
    _ = ∑ k ∈ Finset.Icc 1 (r + 1),
          (n * (psi r k n / (1 - u) ^ (r + k)) +
            u * (psi r k n * ((r + k : ℕ) : ℂ) /
              (1 - u) ^ (r + k + 1))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [show r + k + 1 = (r + k) + 1 by omega, pow_succ]
      field_simp
      ring
    _ = n * (∑ k ∈ Finset.Icc 1 (r + 1),
          psi r k n / (1 - u) ^ (r + k)) +
        u * (∑ k ∈ Finset.Icc 1 (r + 1),
          psi r k n * ((r + k : ℕ) : ℂ) /
            (1 - u) ^ (r + k + 1)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]

private lemma e16ps_one_sub_ne_zero {u : ℂ} (hu : ‖u‖ < 1) : 1 - u ≠ 0 := by
  intro hzero
  have hu1 : u = 1 := (sub_eq_zero.mp hzero).symm
  rw [hu1, norm_one] at hu
  linarith

private lemma e16ps_tsum_eq_P (r : ℕ) (n u : ℂ) (hu : u ∈ e16ps_D) :
    e16ps_G r n u = e16ps_P r n u := by
  induction r generalizing u with
  | zero => exact (e16ps_G_zero n u hu).trans (e16ps_P_zero n u).symm
  | succ r ih =>
    have hEqOn : Set.EqOn (e16ps_G r n) (e16ps_P r n) e16ps_D :=
      fun z hz => ih z hz
    have hlocal : e16ps_G r n =ᶠ[nhds u] e16ps_P r n :=
      hEqOn.eventuallyEq_of_mem (e16ps_isOpen_D.mem_nhds hu)
    have hderiv : deriv (e16ps_G r n) u = deriv (e16ps_P r n) u :=
      hlocal.deriv_eq
    have hmul : (1 - u) * e16ps_G (r + 1) n u =
        (1 - u) * e16ps_P (r + 1) n u := by
      calc
        (1 - u) * e16ps_G (r + 1) n u =
            n * e16ps_G r n u + u * deriv (e16ps_G r n) u :=
          e16ps_G_recurrence r n u hu.1
        _ = n * e16ps_P r n u + u * deriv (e16ps_P r n) u := by
          rw [ih u hu, hderiv]
        _ = (1 - u) * e16ps_P (r + 1) n u :=
          (e16ps_P_recurrence r n u (e16ps_one_sub_ne_zero hu.2)).symm
    exact mul_left_cancel₀ (e16ps_one_sub_ne_zero hu.2) hmul

/-- **Ramanujan's $\psi$-series (Chapter 3, Entry 16).** For natural numbers $r$, $k$ and a complex
number $n$ define $\psi(r, k, n)$ recursively by $\psi(0, 1, n) = 1$, $\psi(0, k, n) = 0$ for
$k \ne 1$, and
$$\psi(r + 1, k, n) = (n - r - k)\, \psi(r, k, n) + (r + k - 1)\, \psi(r, k - 1, n),$$
where the last term is read as $0$ when $k = 0$. Let $r$ be a natural number and let $n$, $u$ be
complex numbers with $|u e^{1-u}| < 1$ and $|u| < 1$. Then the series
$$\sum_{j=0}^{\infty} \frac{(n + j)^{r+j}\, e^{-u(n+j)}\, u^j}{j!}$$
converges unconditionally to
$$\sum_{k=1}^{r+1} \frac{\psi(r, k, n)}{(1 - u)^{r+k}}.$$

The hypothesis $|u| < 1$ selects the component of $\{u : |u e^{1-u}| < 1\}$ containing $0$;
given $|u e^{1-u}| < 1$, it is equivalent to $\operatorname{Re} u < 1$. On the other component
the series converges to a different value.

Proof: Entry 12 gives absolute and locally uniform convergence, and termwise
differentiation gives the recurrence in Berndt (16.4)-(16.5). The Jensen-series
base case from Berndt (16.6) extends to the star-convex domain by analytic uniqueness.

Proves `Wanted` entry `ramanujan_part1_ch3_entry16_psi_series`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, construction and formulas
    (16.4)-(16.5), printed pp. 78-79 / PDF pp. 88-89.
-/
theorem ramanujan_part1_ch3_entry16_psi_series (r : ℕ)
    (n u : ℂ) (h : ‖u * Complex.exp (1 - u)‖ < 1) (hu : ‖u‖ < 1) :
    HasSum (fun j : ℕ => (n + (↑j : ℂ)) ^ (r + j) * Complex.exp (-u * (n + (↑j : ℂ))) * u ^ j /
        (↑(Nat.factorial j) : ℂ)) (∑ k ∈ Finset.Icc 1 (r + 1), psi r k n / (1 - u) ^ (r + k)) := by
  have hsum : HasSum (fun j : ℕ => e16ps_term r n u j) (e16ps_G r n u) := by
    unfold e16ps_G
    exact (e16ps_summable_norm r n u h).of_norm.hasSum
  rw [e16ps_tsum_eq_P r n u ⟨h, hu⟩] at hsum
  simpa [e16ps_term, e16ps_P] using hsum

end Entry16PsiSeries

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
