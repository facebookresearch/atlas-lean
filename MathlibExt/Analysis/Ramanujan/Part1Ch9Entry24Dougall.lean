/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry24Dougall

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9BoundaryLog (x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.log x

def chapter9DilogCosTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.cos ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

def chapter9DilogSinTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.sin ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

private lemma dilogCos_term_eq (rho angle : ℝ) (j : ℕ) :
    chapter9DilogCosTerm rho angle j =
      rho ^ (j + 1) * Real.cos ((((j + 1 : ℕ)) : ℝ) * angle) /
        ((((j + 1 : ℕ)) : ℝ) ^ 2) := rfl

private lemma dilogSin_term_eq (rho angle : ℝ) (j : ℕ) :
    chapter9DilogSinTerm rho angle j =
      rho ^ (j + 1) * Real.sin ((((j + 1 : ℕ)) : ℝ) * angle) /
        ((((j + 1 : ℕ)) : ℝ) ^ 2) := rfl

private lemma summable_inv_succ_sq :
    Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
  have hz : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable
  have h := (summable_nat_add_iff 1).mpr hz
  simpa using h

private lemma summable_dilogCosTerm (rho angle : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    Summable (chapter9DilogCosTerm rho angle) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) summable_inv_succ_sq
  rw [dilogCos_term_eq]
  have hD : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  have habs : |rho| ≤ 1 := abs_le.mpr ⟨by linarith, hrho1⟩
  have hpow : |rho ^ (j + 1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) habs
  have hcos : |Real.cos ((((j + 1 : ℕ)) : ℝ) * angle)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hnum : |rho ^ (j + 1) * Real.cos ((((j + 1 : ℕ)) : ℝ) * angle)| ≤ 1 := by
    calc |rho ^ (j + 1) * Real.cos ((((j + 1 : ℕ)) : ℝ) * angle)|
          = |rho ^ (j + 1)| * |Real.cos ((((j + 1 : ℕ)) : ℝ) * angle)| :=
            abs_mul _ _
      _ ≤ 1 * 1 :=
          mul_le_mul hpow hcos (abs_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hD]
  exact div_le_div_of_nonneg_right hnum (le_of_lt hD)

private lemma summable_dilogSinTerm (rho angle : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    Summable (chapter9DilogSinTerm rho angle) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) summable_inv_succ_sq
  rw [dilogSin_term_eq]
  have hD : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  have habs : |rho| ≤ 1 := abs_le.mpr ⟨by linarith, hrho1⟩
  have hpow : |rho ^ (j + 1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) habs
  have hsin : |Real.sin ((((j + 1 : ℕ)) : ℝ) * angle)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hnum : |rho ^ (j + 1) * Real.sin ((((j + 1 : ℕ)) : ℝ) * angle)| ≤ 1 := by
    calc |rho ^ (j + 1) * Real.sin ((((j + 1 : ℕ)) : ℝ) * angle)|
          = |rho ^ (j + 1)| * |Real.sin ((((j + 1 : ℕ)) : ℝ) * angle)| :=
            abs_mul _ _
      _ ≤ 1 * 1 :=
          mul_le_mul hpow hsin (abs_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hD]
  exact div_le_div_of_nonneg_right hnum (le_of_lt hD)

private lemma boundaryLog_zero : chapter9BoundaryLog 0 = 0 := by simp [chapter9BoundaryLog]

private lemma boundaryLog_one : chapter9BoundaryLog 1 = 0 := by simp [chapter9BoundaryLog]

private lemma tsum_dilogCos_zero (angle : ℝ) :
    ∑' j : ℕ, chapter9DilogCosTerm 0 angle j = 0 := by
  have hfun : chapter9DilogCosTerm 0 angle = fun _ => 0 := by
    funext j
    rw [dilogCos_term_eq]
    simp only [zero_pow (Nat.succ_ne_zero j), zero_mul, zero_div]
  rw [hfun]
  exact tsum_zero

private lemma tsum_dilogSin_zero (angle : ℝ) :
    ∑' j : ℕ, chapter9DilogSinTerm 0 angle j = 0 := by
  have hfun : chapter9DilogSinTerm 0 angle = fun _ => 0 := by
    funext j
    rw [dilogSin_term_eq]
    simp only [zero_pow (Nat.succ_ne_zero j), zero_mul, zero_div]
  rw [hfun]
  exact tsum_zero

private lemma hasSum_dilogCos_one_zero :
    HasSum (chapter9DilogCosTerm 1 0) (Real.pi ^ 2 / 6) := by
  have hcorr : ∑ i ∈ Finset.range 1, (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) i = 0 := by
    simp
  have h2 : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2))
      (Real.pi ^ 2 / 6 +
        ∑ i ∈ Finset.range 1, (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) i) := by
    rw [hcorr, add_zero]
    exact hasSum_zeta_two
  have hbase : HasSum (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
      (Real.pi ^ 2 / 6) :=
    (hasSum_nat_add_iff 1).mpr h2
  have hfun : chapter9DilogCosTerm 1 0 =
      (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext j
    rw [dilogCos_term_eq]
    simp
  rw [hfun]
  exact hbase

private lemma tsum_dilogSin_one_zero : ∑' j : ℕ, chapter9DilogSinTerm 1 0 j = 0 := by
  have hfun : chapter9DilogSinTerm 1 0 = fun _ => 0 := by
    funext j
    rw [dilogSin_term_eq]
    simp
  rw [hfun]
  exact tsum_zero

private lemma exp_I_mul_ofReal (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) =
      ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  have h : (Complex.I * (t : ℂ)) = ((t : ℂ)) * Complex.I := mul_comm _ _
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma re_exp_I_mul (t : ℝ) :
    (Complex.exp (Complex.I * (t : ℂ))).re = Real.cos t := by
  rw [exp_I_mul_ofReal]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

private lemma im_exp_I_mul (t : ℝ) :
    (Complex.exp (Complex.I * (t : ℂ))).im = Real.sin t := by
  rw [exp_I_mul_ofReal]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

private lemma norm_exp_I_mul (t : ℝ) : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

private lemma edge_of_rho_zero {y phi : ℝ} (hy : 0 ≤ y ∧ y ≤ 1)
    (hphi : -Real.pi < phi ∧ phi ≤ Real.pi)
    (hxy : (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) = 1) :
    y = 1 ∧ phi = 0 := by
  have hE : ‖Complex.exp (Complex.I * (phi : ℂ))‖ = 1 := norm_exp_I_mul phi
  have h1 : ‖((y : ℝ) : ℂ)‖ = 1 := by
    have h := congrArg (fun z : ℂ => ‖z‖) hxy
    rw [norm_mul, norm_one] at h
    rw [hE, mul_one] at h
    exact h
  have hy1 : y = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy.1] at h1
    exact h1
  subst hy1
  simp only [Complex.ofReal_one, one_mul] at hxy
  have hcos : Real.cos phi = 1 := by
    have h := congrArg Complex.re hxy
    rw [re_exp_I_mul, Complex.one_re] at h
    exact h
  have hphi0 : phi = 0 := by
    have hmem1 : |phi| ∈ Set.Icc 0 Real.pi :=
      Set.mem_Icc.mpr ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [hphi.1], hphi.2⟩⟩
    have hmem0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi :=
      Set.mem_Icc.mpr ⟨le_refl _, Real.pi_pos.le⟩
    have heq : Real.cos |phi| = Real.cos 0 := by
      rw [Real.cos_abs, hcos, Real.cos_zero]
    have hcon := Real.injOn_cos hmem1 hmem0 heq
    rwa [abs_eq_zero] at hcon
  exact ⟨rfl, hphi0⟩

private lemma summable_cLi2 (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable (fun j : ℕ => z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) summable_inv_succ_sq
  have hnum : ‖z‖ ^ (j + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have hDpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  have hD' : ‖((((j + 1 : ℕ)) : ℂ) ^ 2)‖ = ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    rw [norm_pow, Complex.norm_natCast]
  rw [norm_div, norm_pow, hD']
  exact div_le_div_of_nonneg_right hnum (le_of_lt hDpos)

private lemma cpow_add (rho angle : ℝ) (j : ℕ) :
    (((rho : ℝ) : ℂ) * Complex.exp (Complex.I * (angle : ℂ))) ^ (j + 1)
      = (((rho ^ (j + 1) * Real.cos ((((j + 1 : ℕ)) : ℝ) * angle) : ℝ)) : ℂ)
        + (((rho ^ (j + 1) * Real.sin ((((j + 1 : ℕ)) : ℝ) * angle) : ℝ)) : ℂ) *
          Complex.I := by
  rw [mul_pow]
  have hE : (Complex.exp (Complex.I * (angle : ℂ))) ^ (j + 1)
      = (((Real.cos ((((j + 1 : ℕ)) : ℝ) * angle) : ℝ)) : ℂ)
        + (((Real.sin ((((j + 1 : ℕ)) : ℝ) * angle) : ℝ)) : ℂ) * Complex.I := by
    rw [← Complex.exp_nat_mul]
    have harg : ((j + 1 : ℕ) : ℂ) * (Complex.I * (angle : ℂ))
        = Complex.I * ((((((j + 1 : ℕ)) : ℝ) * angle : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [harg, exp_I_mul_ofReal]
  rw [hE]
  push_cast
  ring

private lemma cLi2_cos (rho angle : ℝ) (j : ℕ) :
    (((((rho : ℝ) : ℂ) * Complex.exp (Complex.I * (angle : ℂ))) ^ (j + 1) /
      ((((j + 1 : ℕ)) : ℂ) ^ 2))).re
      = chapter9DilogCosTerm rho angle j := by
  have hD : ((((j + 1 : ℕ)) : ℂ) ^ 2) =
      ((((((j + 1 : ℕ)) : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [cpow_add, dilogCos_term_eq, hD, div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, sub_zero]
  rw [div_eq_mul_inv]

private lemma cLi2_sin (rho angle : ℝ) (j : ℕ) :
    (((((rho : ℝ) : ℂ) * Complex.exp (Complex.I * (angle : ℂ))) ^ (j + 1) /
      ((((j + 1 : ℕ)) : ℂ) ^ 2))).im
      = chapter9DilogSinTerm rho angle j := by
  have hD : ((((j + 1 : ℕ)) : ℂ) ^ 2) =
      ((((((j + 1 : ℕ)) : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [cpow_add, dilogSin_term_eq, hD, div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  rw [div_eq_mul_inv]

private lemma log_ofReal_mul_exp_I (r t : ℝ) (hr : 0 < r)
    (ht : -Real.pi < t ∧ t ≤ Real.pi) :
    Complex.log (((r : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)))
      = (((Real.log r : ℝ)) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by
  set l : ℂ := (((Real.log r : ℝ)) : ℂ) + ((t : ℝ) : ℂ) * Complex.I with hl
  have hr0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hz : ((r : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)) ≠ 0 :=
    mul_ne_zero hr0 (Complex.exp_ne_zero _)
  have hexp : Complex.exp l
      = ((r : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)) := by
    rw [hl, Complex.exp_add]
    congr 1
    · rw [← Complex.ofReal_exp, Real.exp_log hr]
    · rw [mul_comm ((t : ℝ) : ℂ) Complex.I]
  have himl : l.im = t := by
    rw [hl]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have hlog : Complex.exp (Complex.log (((r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t : ℂ))))
      = ((r : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)) :=
    Complex.exp_log hz
  have h1 : -Real.pi < (Complex.log (((r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t : ℂ)))).im := by
    rw [Complex.log_im]
    exact Complex.neg_pi_lt_arg _
  have h2 : (Complex.log (((r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t : ℂ)))).im ≤ Real.pi := by
    rw [Complex.log_im]
    exact Complex.arg_le_pi _
  have h3 : -Real.pi < l.im := by rw [himl]; exact ht.1
  have h4 : l.im ≤ Real.pi := by rw [himl]; exact ht.2
  have key_eq : Complex.exp (Complex.log (((r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t : ℂ)))) = Complex.exp l :=
    hlog.trans hexp.symm
  exact Complex.exp_inj_of_neg_pi_lt_of_le_pi h1 h2 h3 h4 key_eq

private def cLi2Term (z : ℂ) (j : ℕ) : ℂ :=
  z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)

private def cLi2 (z : ℂ) : ℂ :=
  ∑' j, cLi2Term z j

private def cLi2DerivTerm (z : ℂ) (j : ℕ) : ℂ :=
  z ^ j / ((((j + 1 : ℕ)) : ℂ))

private def cLi2Deriv (z : ℂ) : ℂ :=
  ∑' j, cLi2DerivTerm z j

private def spenceFun (z : ℂ) : ℂ :=
  cLi2 z + cLi2 (1 - z) + Complex.log z * Complex.log (1 - z)

private lemma continuousOn_cLi2 : ContinuousOn cLi2 (Metric.closedBall 0 1) := by
  have hf : ∀ j : ℕ, ContinuousOn (fun z : ℂ => cLi2Term z j)
      (Metric.closedBall 0 1) := by
    intro j
    have hc : Continuous (fun z : ℂ => z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)) :=
      (continuous_id.pow (j + 1)).div_const _
    have heq : (fun z : ℂ => cLi2Term z j)
        = (fun z : ℂ => z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)) := rfl
    rw [heq]
    exact hc.continuousOn
  have hbound : ∀ (j : ℕ) (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) 1 →
      ‖cLi2Term z j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    intro j z hz
    have hnorm : ‖z‖ ≤ 1 := by
      have hdist : dist z (0 : ℂ) ≤ 1 := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm, sub_zero] at hdist
    have hnum : ‖z‖ ^ (j + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hnorm
    have hDpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by positivity
    have hD' : ‖((((j + 1 : ℕ)) : ℂ) ^ 2)‖ = ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
      rw [norm_pow, Complex.norm_natCast]
    have hterm : ‖cLi2Term z j‖ = ‖z‖ ^ (j + 1) / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
      unfold cLi2Term
      rw [norm_div, norm_pow, hD']
    rw [hterm]
    exact div_le_div_of_nonneg_right hnum (le_of_lt hDpos)
  have hcont := continuousOn_tsum hf summable_inv_succ_sq hbound
  have heq : (fun x : ℂ => ∑' n, cLi2Term x n) = cLi2 := rfl
  rw [heq] at hcont
  exact hcont

private lemma cLi2_zero : cLi2 0 = 0 := by
  have hfun : (fun j : ℕ => cLi2Term (0 : ℂ) j) = fun _ => 0 := by
    funext j
    unfold cLi2Term
    simp only [zero_pow (Nat.succ_ne_zero j), zero_div]
  unfold cLi2
  rw [hfun]
  exact tsum_zero

private lemma hasSum_real_succ_sq :
    HasSum (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
      (Real.pi ^ 2 / 6) := by
  have hcorr : ∑ i ∈ Finset.range 1, (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) i = 0 := by
    simp
  have h2 : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2))
      (Real.pi ^ 2 / 6 +
        ∑ i ∈ Finset.range 1, (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) i) := by
    rw [hcorr, add_zero]
    exact hasSum_zeta_two
  exact (hasSum_nat_add_iff 1).mpr h2

private lemma cLi2_one : cLi2 1 = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
  have hbase := hasSum_real_succ_sq
  have hc : HasSum (fun j : ℕ => (((1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) : ℝ) : ℂ))
      (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) :=
    (Complex.hasSum_ofReal).mpr hbase
  have hfun : (fun j : ℕ => cLi2Term (1 : ℂ) j)
      = (fun j : ℕ => (((1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) : ℝ) : ℂ)) := by
    funext j
    unfold cLi2Term
    simp only [one_pow]
    have hD : ((((j + 1 : ℕ)) : ℂ) ^ 2)
        = ((((((j + 1 : ℕ)) : ℝ) ^ 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hD, ← Complex.ofReal_one, ← Complex.ofReal_div]
  rw [← hfun] at hc
  unfold cLi2
  exact hc.tsum_eq

private lemma hasDerivAt_cLi2Term (j : ℕ) (y : ℂ) :
    HasDerivAt (fun z : ℂ => cLi2Term z j) (cLi2DerivTerm y j) y := by
  have hj : ((((j + 1 : ℕ)) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero j
  have hpow := hasDerivAt_pow (j + 1) y
  simp only [Nat.add_sub_cancel] at hpow
  have hdiv := hpow.div_const ((((j + 1 : ℕ)) : ℂ) ^ 2)
  have heq : ((((j + 1 : ℕ)) : ℂ) * y ^ j) / ((((j + 1 : ℕ)) : ℂ) ^ 2)
      = cLi2DerivTerm y j := by
    unfold cLi2DerivTerm
    field_simp
  rw [heq] at hdiv
  have hfun : (fun z : ℂ => cLi2Term z j)
      = (fun z : ℂ => z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)) := rfl
  rw [hfun]
  exact hdiv

private lemma norm_cLi2DerivTerm_le (r : ℝ) (j : ℕ) (y : ℂ) (hy : ‖y‖ < r) :
    ‖cLi2DerivTerm y j‖ ≤ r ^ j := by
  unfold cLi2DerivTerm
  have hD : ‖((((j + 1 : ℕ)) : ℂ))‖ = ((((j + 1 : ℕ)) : ℝ)) := Complex.norm_natCast _
  have h1 : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
    have hj : (1 : ℕ) ≤ j + 1 := Nat.le_add_left 1 j
    exact_mod_cast hj
  have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) := lt_of_lt_of_le zero_lt_one h1
  rw [norm_div, norm_pow, hD]
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (le_of_lt hy)
  have hpow : ‖y‖ ^ j ≤ r ^ j :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hy) j
  calc ‖y‖ ^ j / ((((j + 1 : ℕ)) : ℝ))
      ≤ r ^ j / ((((j + 1 : ℕ)) : ℝ)) :=
        div_le_div_of_nonneg_right hpow (le_of_lt hpos)
    _ ≤ r ^ j := div_le_self (pow_nonneg hr0 _) h1

private lemma hasDerivAt_cLi2 {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt cLi2 (cLi2Deriv z) z := by
  set r : ℝ := (1 + ‖z‖) / 2 with hr
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hr0 : 0 < r := by
    rw [hr]
    linarith
  have hzr : ‖z‖ < r := by
    rw [hr]
    linarith
  have hr1 : r < 1 := by
    rw [hr]
    linarith
  have hu : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one (le_of_lt hr0) hr1
  have ht : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have hprec : IsPreconnected (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).isPreconnected
  have hg : ∀ (j : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) r →
      HasDerivAt (fun z : ℂ => cLi2Term z j) (cLi2DerivTerm y j) y := by
    intro j y _
    exact hasDerivAt_cLi2Term j y
  have hg' : ∀ (j : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) r →
      ‖cLi2DerivTerm y j‖ ≤ r ^ j := by
    intro j y hy
    have hnorm : ‖y‖ < r := by
      have hdist : dist y (0 : ℂ) < r := Metric.mem_ball.mp hy
      rwa [dist_eq_norm, sub_zero] at hdist
    exact norm_cLi2DerivTerm_le r j y hnorm
  have hy0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_self]
    exact hr0
  have hg0 : Summable (fun j : ℕ => cLi2Term (0 : ℂ) j) := by
    have hfun : (fun j : ℕ => cLi2Term (0 : ℂ) j) = fun _ => 0 := by
      funext j
      unfold cLi2Term
      simp only [zero_pow (Nat.succ_ne_zero j), zero_div]
    rw [hfun]
    exact summable_zero
  have hy : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact hzr
  have hmain := hasDerivAt_tsum_of_isPreconnected (u := fun j : ℕ => r ^ j)
    (t := Metric.ball (0 : ℂ) r) (y₀ := (0 : ℂ)) (y := z)
    hu ht hprec hg hg' hy0 hg0 hy
  have heq1 : (fun z : ℂ => ∑' n, cLi2Term z n) = cLi2 := rfl
  have heq2 : (∑' n, cLi2DerivTerm z n) = cLi2Deriv z := rfl
  rw [heq1, heq2] at hmain
  exact hmain

private lemma summable_cLi2Deriv {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun j : ℕ => cLi2DerivTerm z j) := by
  set r : ℝ := (1 + ‖z‖) / 2 with hr
  have hzr : ‖z‖ < r := by
    rw [hr]
    linarith [norm_nonneg z, hz]
  have hr1 : r < 1 := by
    rw [hr]
    linarith [hz]
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (le_of_lt hzr)
  have hu : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one hr0 hr1
  exact Summable.of_norm_bounded hu (fun j => norm_cLi2DerivTerm_le r j z hzr)

private lemma mul_cLi2Deriv {z : ℂ} (hz : ‖z‖ < 1) :
    z * cLi2Deriv z = -Complex.log (1 - z) := by
  have hsumm := summable_cLi2Deriv hz
  have hlog := Complex.hasSum_taylorSeries_neg_log' hz
  have hcast : ∀ n : ℕ, ((((n + 1 : ℕ)) : ℂ)) = ((n : ℂ) + 1) := by
    intro n
    push_cast
    ring
  have hlog2 : HasSum (fun n : ℕ => z ^ (n + 1) / ((((n + 1 : ℕ)) : ℂ)))
      (-Complex.log (1 - z)) := by
    have hfun : (fun n : ℕ => z ^ (n + 1) / ((((n + 1 : ℕ)) : ℂ)))
        = (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1)) := by
      funext n
      rw [hcast]
    rw [hfun]
    convert hlog using 2
  have hmul : z * cLi2Deriv z
      = ∑' j, z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ)) := by
    unfold cLi2Deriv
    rw [← hsumm.tsum_mul_left z]
    refine tsum_congr fun j => ?_
    unfold cLi2DerivTerm
    rw [← mul_div_assoc, ← pow_succ']
  rw [hmul]
  exact hlog2.tsum_eq

private def openLens : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1

private lemma isOpen_openLens : IsOpen openLens :=
  Metric.isOpen_ball.inter Metric.isOpen_ball

private lemma convex_openLens : Convex ℝ openLens :=
  (convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) 1)

private lemma isPreconnected_openLens : IsPreconnected openLens :=
  convex_openLens.isPreconnected

private lemma norm_lt_one_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    ‖z‖ < 1 := by
  have h0 : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
  have hdist : dist z (0 : ℂ) < 1 := Metric.mem_ball.mp h0
  rwa [dist_eq_norm, sub_zero] at hdist

private lemma norm_one_sub_lt_one_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    ‖(1 : ℂ) - z‖ < 1 := by
  have h1 : z ∈ Metric.ball (1 : ℂ) 1 := hz.2
  have hdist : dist z (1 : ℂ) < 1 := Metric.mem_ball.mp h1
  rw [dist_eq_norm] at hdist
  have hrev : ‖(1 : ℂ) - z‖ = ‖z - 1‖ := norm_sub_rev _ _
  rwa [hrev]

private lemma re_pos_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    0 < z.re := by
  have h1 := norm_one_sub_lt_one_of_mem_openLens hz
  have hle : |(1 - z).re| ≤ ‖(1 : ℂ) - z‖ := Complex.abs_re_le_norm _
  have hlt : |(1 - z).re| < 1 := lt_of_le_of_lt hle h1
  have hre : (1 - z).re = 1 - z.re := by simp
  rw [hre] at hlt
  have hmem := abs_lt.mp hlt
  linarith

private lemma re_one_sub_pos_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    0 < (1 - z).re := by
  have h0 := norm_lt_one_of_mem_openLens hz
  have hle : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm _
  have hlt : |z.re| < 1 := lt_of_le_of_lt hle h0
  have hmem := abs_lt.mp hlt
  have hre : (1 - z).re = 1 - z.re := by simp
  rw [hre]
  linarith

private lemma mem_slitPlane_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (re_pos_of_mem_openLens hz)

private lemma one_sub_mem_slitPlane_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    (1 : ℂ) - z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (re_one_sub_pos_of_mem_openLens hz)

private lemma ne_zero_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    z ≠ 0 :=
  Complex.slitPlane_ne_zero (mem_slitPlane_of_mem_openLens hz)

private lemma one_sub_ne_zero_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    (1 : ℂ) - z ≠ 0 :=
  Complex.slitPlane_ne_zero (one_sub_mem_slitPlane_of_mem_openLens hz)

private lemma hasDerivAt_one_sub (z : ℂ) :
    HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) z := by
  have h := (hasDerivAt_id' z).const_sub (1 : ℂ)
  simpa using h

private lemma deriv_spenceFun_eq_zero {z : ℂ} (hz : z ∈ openLens) :
    deriv spenceFun z = 0 := by
  have hz0 : ‖z‖ < 1 := norm_lt_one_of_mem_openLens hz
  have hz1 : ‖(1 : ℂ) - z‖ < 1 := norm_one_sub_lt_one_of_mem_openLens hz
  have hL1 : HasDerivAt cLi2 (cLi2Deriv z) z := hasDerivAt_cLi2 hz0
  have hL1' : HasDerivAt cLi2 (cLi2Deriv (1 - z)) (1 - z) :=
    hasDerivAt_cLi2 hz1
  have hsub := hasDerivAt_one_sub z
  have hL2 : HasDerivAt (cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w))
      (cLi2Deriv (1 - z) * (-1)) z :=
    hL1'.comp z hsub
  have hlog1 : HasDerivAt Complex.log z⁻¹ z :=
    Complex.hasDerivAt_log (mem_slitPlane_of_mem_openLens hz)
  have hlog_outer : HasDerivAt Complex.log ((1 - z)⁻¹) (1 - z) :=
    Complex.hasDerivAt_log (one_sub_mem_slitPlane_of_mem_openLens hz)
  have hlog2 : HasDerivAt (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))
      (((1 - z)⁻¹) * (-1)) z :=
    hlog_outer.comp z hsub
  have hprod : HasDerivAt (Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w)))
      (z⁻¹ * Complex.log (1 - z) + Complex.log z * (((1 - z)⁻¹) * (-1))) z :=
    hlog1.mul hlog2
  have hsum : HasDerivAt (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
      + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w)))
      ((cLi2Deriv z + cLi2Deriv (1 - z) * (-1))
        + (z⁻¹ * Complex.log (1 - z)
          + Complex.log z * (((1 - z)⁻¹) * (-1)))) z :=
    (hL1.add hL2).add hprod
  have hfun : spenceFun
      = (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
        + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))) := by
    funext w
    unfold spenceFun
    simp [Function.comp, Pi.add_apply, Pi.mul_apply]
  rw [hfun]
  have hderiv := hsum.deriv
  rw [hderiv]
  have hC1 : z * cLi2Deriv z = -Complex.log (1 - z) := mul_cLi2Deriv hz0
  have hC2 : (1 - z) * cLi2Deriv (1 - z) = -Complex.log (1 - (1 - z)) :=
    mul_cLi2Deriv hz1
  have hsub2 : (1 : ℂ) - (1 - z) = z := by ring
  rw [hsub2] at hC2
  have hzne : z ≠ 0 := ne_zero_of_mem_openLens hz
  have h1ne : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem_openLens hz
  have e1 : z⁻¹ * Complex.log (1 - z) = -cLi2Deriv z := by
    have h := congrArg (fun w : ℂ => z⁻¹ * w) hC1
    simp only [← mul_assoc, inv_mul_cancel₀ hzne, one_mul, mul_neg] at h
    have h2 : cLi2Deriv z = -(z⁻¹ * Complex.log (1 - z)) := h
    calc z⁻¹ * Complex.log (1 - z)
        = -(-(z⁻¹ * Complex.log (1 - z))) := (neg_neg _).symm
      _ = -cLi2Deriv z := by rw [← h2]
  have e2 : Complex.log z * (((1 - z)⁻¹) * (-1)) = cLi2Deriv (1 - z) := by
    have h := congrArg (fun w : ℂ => (1 - z)⁻¹ * w) hC2
    simp only [← mul_assoc, inv_mul_cancel₀ h1ne, one_mul, mul_neg] at h
    have hlogeq : (1 - z)⁻¹ * Complex.log z = -cLi2Deriv (1 - z) := by
      have h2 : cLi2Deriv (1 - z) = -((1 - z)⁻¹ * Complex.log z) := h
      calc (1 - z)⁻¹ * Complex.log z
          = -(-((1 - z)⁻¹ * Complex.log z)) := (neg_neg _).symm
        _ = -cLi2Deriv (1 - z) := by rw [← h2]
    calc Complex.log z * (((1 - z)⁻¹) * (-1))
        = -((1 - z)⁻¹ * Complex.log z) := by ring
      _ = -(-cLi2Deriv (1 - z)) := by rw [hlogeq]
      _ = cLi2Deriv (1 - z) := neg_neg _
  calc (cLi2Deriv z + cLi2Deriv (1 - z) * (-1))
        + (z⁻¹ * Complex.log (1 - z)
          + Complex.log z * (((1 - z)⁻¹) * (-1)))
      = (cLi2Deriv z + (-cLi2Deriv (1 - z))) + ((-cLi2Deriv z) + cLi2Deriv (1 - z)) := by
        rw [e1, e2]
        ring
    _ = 0 := by ring

private lemma differentiableOn_spenceFun :
    DifferentiableOn ℂ spenceFun openLens := by
  intro z hz
  have hz0 : ‖z‖ < 1 := norm_lt_one_of_mem_openLens hz
  have hz1 : ‖(1 : ℂ) - z‖ < 1 := norm_one_sub_lt_one_of_mem_openLens hz
  have hL1 : HasDerivAt cLi2 (cLi2Deriv z) z := hasDerivAt_cLi2 hz0
  have hL1' : HasDerivAt cLi2 (cLi2Deriv (1 - z)) (1 - z) :=
    hasDerivAt_cLi2 hz1
  have hsub := hasDerivAt_one_sub z
  have hL2 : HasDerivAt (cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w))
      (cLi2Deriv (1 - z) * (-1)) z :=
    hL1'.comp z hsub
  have hlog1 : HasDerivAt Complex.log z⁻¹ z :=
    Complex.hasDerivAt_log (mem_slitPlane_of_mem_openLens hz)
  have hlog_outer : HasDerivAt Complex.log ((1 - z)⁻¹) (1 - z) :=
    Complex.hasDerivAt_log (one_sub_mem_slitPlane_of_mem_openLens hz)
  have hlog2 : HasDerivAt (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))
      (((1 - z)⁻¹) * (-1)) z :=
    hlog_outer.comp z hsub
  have hprod : HasDerivAt (Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w)))
      (z⁻¹ * Complex.log (1 - z) + Complex.log z * (((1 - z)⁻¹) * (-1))) z :=
    hlog1.mul hlog2
  have hsum : HasDerivAt (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
      + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w)))
      ((cLi2Deriv z + cLi2Deriv (1 - z) * (-1))
        + (z⁻¹ * Complex.log (1 - z)
          + Complex.log z * (((1 - z)⁻¹) * (-1)))) z :=
    (hL1.add hL2).add hprod
  have hfun : spenceFun
      = (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
        + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))) := by
    funext w
    unfold spenceFun
    simp [Function.comp, Pi.add_apply, Pi.mul_apply]
  have hdiff : DifferentiableAt ℂ
      (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
        + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))) z :=
    hsum.differentiableAt
  have hdiff2 : DifferentiableAt ℂ spenceFun z := hfun.symm ▸ hdiff
  exact hdiff2.differentiableWithinAt

private lemma spenceFun_const_on_openLens :
    ∃ C : ℂ, ∀ z ∈ openLens, spenceFun z = C :=
  isOpen_openLens.exists_is_const_of_deriv_eq_zero isPreconnected_openLens
    differentiableOn_spenceFun (fun _ hz => deriv_spenceFun_eq_zero hz)

private def seqT : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)

private lemma seqT_pos (n : ℕ) : 0 < seqT n := by
  unfold seqT
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  exact one_div_pos.mpr hpos

private lemma seqT_le_half (n : ℕ) : seqT n ≤ 1 / 2 := by
  unfold seqT
  have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  exact one_div_le_one_div_of_le (by norm_num) h2

private lemma seqT_lt_one (n : ℕ) : seqT n < 1 := by
  calc seqT n ≤ 1 / 2 := seqT_le_half n
    _ < 1 := by norm_num

private lemma tendsto_seqT : Tendsto seqT atTop (𝓝 0) := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun n : ℕ => (((n : ℝ) + 2)⁻¹ : ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hfun : seqT = (fun n : ℕ => (((n : ℝ) + 2)⁻¹ : ℝ)) := by
    funext n
    unfold seqT
    rw [one_div]
  rw [hfun]
  exact h0

private def seqU : ℕ → ℂ := fun n => ((seqT n : ℝ) : ℂ)

private lemma seqU_mem_openLens (n : ℕ) : seqU n ∈ openLens := by
  have ht0 : 0 < seqT n := seqT_pos n
  have ht1 : seqT n < 1 := seqT_lt_one n
  have ht_half : seqT n ≤ 1 / 2 := seqT_le_half n
  constructor
  · rw [Metric.mem_ball, dist_eq_norm]
    have hsub : seqU n - 0 = seqU n := sub_zero _
    rw [hsub]
    unfold seqU
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact ht1
  · rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖seqU n - 1‖ = 1 - seqT n := by
      have heq : seqU n - 1 = ((((seqT n - 1 : ℝ))) : ℂ) := by
        unfold seqU
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      have hneg : seqT n - 1 < 0 := by linarith
      rw [abs_of_neg hneg]
      ring
    rw [hnorm]
    linarith

private lemma tendsto_seqU : Tendsto seqU atTop (𝓝 0) := by
  have h0 := tendsto_seqT
  have hcont := Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hcomp : Tendsto (fun n : ℕ => (((seqT n : ℝ)) : ℂ)) atTop
      (𝓝 (((0 : ℝ)) : ℂ)) :=
    hcont.comp h0
  have hzero : (((0 : ℝ)) : ℂ) = (0 : ℂ) := Complex.ofReal_zero
  rw [hzero] at hcomp
  have hfun : seqU = (fun n : ℕ => (((seqT n : ℝ)) : ℂ)) := rfl
  rw [hfun]
  exact hcomp

private lemma tendsto_one_sub_seqU : Tendsto (fun n : ℕ => (1 : ℂ) - seqU n)
    atTop (𝓝 1) := by
  have hU := tendsto_seqU
  have h1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub := h1.sub hU
  have hzero : (1 : ℂ) - 0 = 1 := sub_zero _
  rw [hzero] at hsub
  exact hsub

private lemma seqU_mem_closedBall (n : ℕ) :
    seqU n ∈ Metric.closedBall (0 : ℂ) 1 :=
  Metric.ball_subset_closedBall (seqU_mem_openLens n).1

private lemma one_sub_seqU_mem_closedBall (n : ℕ) :
    (1 : ℂ) - seqU n ∈ Metric.closedBall (0 : ℂ) 1 := by
  have ht0 : 0 < seqT n := seqT_pos n
  have ht1 : seqT n < 1 := seqT_lt_one n
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : ((1 : ℂ) - seqU n) - 0 = (1 : ℂ) - seqU n := sub_zero _
  rw [hsub]
  have heq : (1 : ℂ) - seqU n = ((((1 - seqT n : ℝ))) : ℂ) := by
    unfold seqU
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have hpos : (0 : ℝ) < 1 - seqT n := by linarith
  rw [abs_of_pos hpos]
  linarith

private lemma zero_mem_closedBall_one : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_self]
  norm_num

private lemma one_mem_closedBall_one : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : (1 : ℂ) - 0 = 1 := sub_zero _
  rw [hsub, norm_one]

private lemma tendsto_cLi2_seqU : Tendsto (fun n : ℕ => cLi2 (seqU n))
    atTop (𝓝 (cLi2 0)) := by
  have hcont : ContinuousWithinAt cLi2 (Metric.closedBall (0 : ℂ) 1) 0 :=
    continuousOn_cLi2.continuousWithinAt zero_mem_closedBall_one
  have hwithin : Tendsto seqU atTop (𝓝[Metric.closedBall (0 : ℂ) 1] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within seqU tendsto_seqU
      (Eventually.of_forall seqU_mem_closedBall)
  have hcomp : Tendsto (cLi2 ∘ seqU) atTop (𝓝 (cLi2 0)) :=
    hcont.tendsto.comp hwithin
  have hfun : (cLi2 ∘ seqU) = (fun n : ℕ => cLi2 (seqU n)) := rfl
  rw [hfun] at hcomp
  exact hcomp

private lemma tendsto_cLi2_one_sub_seqU : Tendsto (fun n : ℕ => cLi2 ((1 : ℂ) - seqU n))
    atTop (𝓝 (cLi2 1)) := by
  have hcont : ContinuousWithinAt cLi2 (Metric.closedBall (0 : ℂ) 1) 1 :=
    continuousOn_cLi2.continuousWithinAt one_mem_closedBall_one
  have hwithin : Tendsto (fun n : ℕ => (1 : ℂ) - seqU n) atTop
      (𝓝[Metric.closedBall (0 : ℂ) 1] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_sub_seqU (Eventually.of_forall one_sub_seqU_mem_closedBall)
  have hcomp : Tendsto (cLi2 ∘ (fun n : ℕ => (1 : ℂ) - seqU n)) atTop
      (𝓝 (cLi2 1)) :=
    hcont.tendsto.comp hwithin
  have hfun : (cLi2 ∘ (fun n : ℕ => (1 : ℂ) - seqU n))
      = (fun n : ℕ => cLi2 ((1 : ℂ) - seqU n)) := rfl
  rw [hfun] at hcomp
  exact hcomp

private lemma abs_log_one_sub_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    |Real.log (1 - t)| ≤ 2 * t := by
  have hu_pos : (0 : ℝ) < 1 - t := by linarith
  have h1 : Real.log (1 - t) ≤ (1 - t) - 1 :=
    Real.log_le_sub_one_of_pos hu_pos
  have h2 : 1 - (1 - t)⁻¹ ≤ Real.log (1 - t) :=
    Real.one_sub_inv_le_log_of_pos hu_pos
  have hlog_nonpos : Real.log (1 - t) ≤ 0 := by linarith
  have habs : |Real.log (1 - t)| = -Real.log (1 - t) :=
    abs_of_nonpos hlog_nonpos
  rw [habs]
  have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by
    field_simp
    ring
  have hle : -Real.log (1 - t) ≤ t / (1 - t) := by
    have h2' : -Real.log (1 - t) ≤ (1 - t)⁻¹ - 1 := by linarith
    rw [heq] at h2'
    exact h2'
  have hdiv : t / (1 - t) ≤ 2 * t := by
    rw [div_le_iff₀ hu_pos]
    have ht_nonneg : (0 : ℝ) ≤ t := le_of_lt ht0
    nlinarith [ht_nonneg, ht1, hu_pos]
  exact le_trans hle hdiv

private lemma tendsto_mul_log_seqT :
    Tendsto (fun n : ℕ => seqT n * Real.log (seqT n)) atTop (𝓝 0) := by
  have hcont : Continuous (fun x : ℝ => x * Real.log x) :=
    Real.continuous_mul_log
  have hcomp : Tendsto ((fun x : ℝ => x * Real.log x) ∘ seqT) atTop
      (𝓝 ((0 : ℝ) * Real.log 0)) :=
    (hcont.tendsto 0).comp tendsto_seqT
  have h0val : (0 : ℝ) * Real.log 0 = 0 := zero_mul _
  rw [h0val] at hcomp
  have hfun : ((fun x : ℝ => x * Real.log x) ∘ seqT)
      = (fun n : ℕ => seqT n * Real.log (seqT n)) := rfl
  rw [hfun] at hcomp
  exact hcomp

private lemma tendsto_log_prod_seqU :
    Tendsto (fun n : ℕ => Complex.log (seqU n) * Complex.log ((1 : ℂ) - seqU n))
      atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ,
      ‖Complex.log (seqU n) * Complex.log ((1 : ℂ) - seqU n)‖
        ≤ 2 * |seqT n * Real.log (seqT n)| := by
    intro n
    have ht0 : 0 < seqT n := seqT_pos n
    have ht1 : seqT n ≤ 1 / 2 := seqT_le_half n
    have hlog1 : Complex.log (seqU n) = (((Real.log (seqT n) : ℝ)) : ℂ) := by
      have h := Complex.ofReal_log (le_of_lt ht0)
      unfold seqU at *
      rw [← h]
    have heq2 : (1 : ℂ) - seqU n = ((((1 - seqT n : ℝ))) : ℂ) := by
      unfold seqU
      push_cast
      ring
    have h1t : (0 : ℝ) ≤ 1 - seqT n := by linarith [seqT_lt_one n]
    have hlog2 : Complex.log ((1 : ℂ) - seqU n)
        = (((Real.log (1 - seqT n) : ℝ)) : ℂ) := by
      rw [heq2, ← Complex.ofReal_log h1t]
    rw [hlog1, hlog2, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    have hblog := abs_log_one_sub_le ht0 ht1
    have ht_abs : |seqT n| = seqT n := abs_of_pos ht0
    have hmul_abs : |seqT n * Real.log (seqT n)|
        = seqT n * |Real.log (seqT n)| := by
      rw [abs_mul, ht_abs]
    rw [hmul_abs]
    calc |Real.log (seqT n)| * |Real.log (1 - seqT n)|
        ≤ |Real.log (seqT n)| * (2 * seqT n) := by
          apply mul_le_mul_of_nonneg_left hblog (abs_nonneg _)
      _ = 2 * (seqT n * |Real.log (seqT n)|) := by ring
  have hbase := tendsto_mul_log_seqT
  have habs : Tendsto (fun n : ℕ => |seqT n * Real.log (seqT n)|) atTop (𝓝 0) := by
    have h := hbase.abs
    simpa using h
  have h2 : Tendsto (fun n : ℕ => 2 * |seqT n * Real.log (seqT n)|) atTop
      (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have hmul := hconst.mul habs
    have h20 : (2 : ℝ) * 0 = 0 := mul_zero _
    rw [h20] at hmul
    exact hmul
  exact squeeze_zero_norm' (Eventually.of_forall hbound) h2

private lemma tendsto_spenceFun_seqU :
    Tendsto (fun n : ℕ => spenceFun (seqU n)) atTop
      (𝓝 (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) := by
  have h1 := tendsto_cLi2_seqU
  have h2 := tendsto_cLi2_one_sub_seqU
  have h3 := tendsto_log_prod_seqU
  have hadd := h1.add h2
  have hall := hadd.add h3
  have h0eq : cLi2 (0 : ℂ) = 0 := cLi2_zero
  have h1eq : cLi2 (1 : ℂ) = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := cLi2_one
  rw [h0eq, h1eq] at hall
  have hval : ((0 : ℂ) + (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) + (0 : ℂ)
      = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
    simp
  rw [hval] at hall
  have hfun : (fun n : ℕ => spenceFun (seqU n))
      = (fun n : ℕ => (cLi2 (seqU n) + cLi2 ((1 : ℂ) - seqU n)
        + Complex.log (seqU n) * Complex.log ((1 : ℂ) - seqU n))) := rfl
  rw [hfun]
  have hall2 : Tendsto (fun n : ℕ => (cLi2 (seqU n) + cLi2 ((1 : ℂ) - seqU n)
      + Complex.log (seqU n) * Complex.log ((1 : ℂ) - seqU n))) atTop
      (𝓝 (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) := hall
  exact hall2

private lemma spenceFun_eq_pi_sq_on_openLens :
    ∀ z ∈ openLens, spenceFun z = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
  obtain ⟨C, hC⟩ := spenceFun_const_on_openLens
  have hlim := tendsto_spenceFun_seqU
  have hfun : (fun n : ℕ => spenceFun (seqU n)) = fun _ => C := by
    funext n
    exact hC _ (seqU_mem_openLens n)
  have hconst : Tendsto (fun n : ℕ => spenceFun (seqU n)) atTop (𝓝 C) := by
    rw [hfun]
    exact tendsto_const_nhds
  have hCEq : C = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) :=
    tendsto_nhds_unique hconst hlim
  intro z hz
  rw [hC z hz, hCEq]

private def closedLens : Set ℂ :=
  Metric.closedBall (0 : ℂ) 1 ∩ Metric.closedBall (1 : ℂ) 1

private lemma norm_le_one_of_mem_closedLens {z : ℂ} (hz : z ∈ closedLens) :
    ‖z‖ ≤ 1 := by
  have h0 : z ∈ Metric.closedBall (0 : ℂ) 1 := hz.1
  have hdist : dist z (0 : ℂ) ≤ 1 := Metric.mem_closedBall.mp h0
  rwa [dist_eq_norm, sub_zero] at hdist

private lemma norm_one_sub_le_one_of_mem_closedLens {z : ℂ}
    (hz : z ∈ closedLens) : ‖(1 : ℂ) - z‖ ≤ 1 := by
  have h1 : z ∈ Metric.closedBall (1 : ℂ) 1 := hz.2
  have hdist : dist z (1 : ℂ) ≤ 1 := Metric.mem_closedBall.mp h1
  rw [dist_eq_norm] at hdist
  have hrev : ‖(1 : ℂ) - z‖ = ‖z - 1‖ := norm_sub_rev _ _
  rwa [hrev]

private lemma re_pos_of_mem_closedLens {w : ℂ}
    (hw1 : ‖(1 : ℂ) - w‖ ≤ 1) (hwne : w ≠ 0) : 0 < w.re := by
  by_contra hneg
  push Not at hneg
  have hle : w.re ≤ 0 := hneg
  have hsq : ‖(1 : ℂ) - w‖ ^ 2
      = (1 - w.re) * (1 - w.re) + w.im * w.im := by
    have hdef : ‖(1 : ℂ) - w‖ ^ 2
        = ((1 - w).re) * ((1 - w).re) + ((1 - w).im) * ((1 - w).im) :=
      RCLike.norm_sq_eq_def
    have hre : ((1 : ℂ) - w).re = 1 - w.re := by simp
    have him : ((1 : ℂ) - w).im = -w.im := by simp
    rw [hre, him] at hdef
    have hnegmul : (-w.im) * (-w.im) = w.im * w.im := by ring
    rw [hnegmul] at hdef
    exact hdef
  have hsq_le : ‖(1 : ℂ) - w‖ ^ 2 ≤ 1 := by
    have hnn : (0 : ℝ) ≤ ‖(1 : ℂ) - w‖ := norm_nonneg _
    calc ‖(1 : ℂ) - w‖ ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ hnn hw1 2
      _ = 1 := one_pow _
  have hsum_le : (1 - w.re) * (1 - w.re) + w.im * w.im ≤ 1 := by
    rw [← hsq]
    exact hsq_le
  have h1a : (1 : ℝ) ≤ 1 - w.re := by linarith
  have hsq1 : (1 : ℝ) ≤ (1 - w.re) * (1 - w.re) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ (1 - w.re) * (1 - w.re) :=
          mul_le_mul h1a h1a (by norm_num) (by linarith)
  have hbb : (0 : ℝ) ≤ w.im * w.im := mul_self_nonneg _
  have hXeq : (1 - w.re) * (1 - w.re) = 1 := by
    have hXle : (1 - w.re) * (1 - w.re) ≤ 1 := by linarith
    exact le_antisymm hXle hsq1
  have hYeq : w.im * w.im = 0 := by linarith
  have him0 : w.im = 0 := mul_self_eq_zero.mp hYeq
  have hre0 : w.re = 0 := by
    have haa : w.re * (w.re - 2) = 0 := by
      have hring : w.re * (w.re - 2)
          = (1 - w.re) * (1 - w.re) - 1 := by ring
      rw [hring, hXeq, sub_self]
    have hor := mul_eq_zero.mp haa
    rcases hor with h0 | h2
    · exact h0
    · have h2eq : w.re = 2 := by linarith
      linarith
  have hw0 : w = 0 := by
    rw [Complex.ext_iff]
    simp [hre0, him0]
  exact hwne hw0

private lemma mem_slitPlane_of_mem_closedLens {z : ℂ} (hz : z ∈ closedLens)
    (hne : z ≠ 0) : z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (re_pos_of_mem_closedLens
    (norm_one_sub_le_one_of_mem_closedLens hz) hne)

private lemma one_sub_mem_slitPlane_of_mem_closedLens {z : ℂ}
    (hz : z ∈ closedLens) (hne : (1 : ℂ) - z ≠ 0) :
    (1 : ℂ) - z ∈ Complex.slitPlane := by
  have hz0 : ‖z‖ ≤ 1 := norm_le_one_of_mem_closedLens hz
  have h1 : ‖(1 : ℂ) - ((1 : ℂ) - z)‖ ≤ 1 := by
    have heq : (1 : ℂ) - ((1 : ℂ) - z) = z := by ring
    rw [heq]
    exact hz0
  have hpos : 0 < ((1 : ℂ) - z).re :=
    re_pos_of_mem_closedLens h1 hne
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl hpos

private def blendSeq (z0 : ℂ) : ℕ → ℂ := fun n =>
  (((1 - seqT n : ℝ)) : ℂ) * z0 + ((((seqT n / 2 : ℝ))) : ℂ)

private lemma blendSeq_mem_openLens {z0 : ℂ} (hz : z0 ∈ closedLens)
    (n : ℕ) : blendSeq z0 n ∈ openLens := by
  have ht0 : 0 < seqT n := seqT_pos n
  have ht_half : seqT n ≤ 1 / 2 := seqT_le_half n
  have h1t_nonneg : (0 : ℝ) ≤ 1 - seqT n := by
    have ht1 : seqT n < 1 := seqT_lt_one n
    linarith
  have hz0 : ‖z0‖ ≤ 1 := norm_le_one_of_mem_closedLens hz
  have hz1 : ‖(1 : ℂ) - z0‖ ≤ 1 := norm_one_sub_le_one_of_mem_closedLens hz
  have hn1 : ‖((((1 - seqT n : ℝ))) : ℂ)‖ = 1 - seqT n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1t_nonneg]
  have hn2 : ‖((((seqT n / 2 : ℝ))) : ℂ)‖ = seqT n / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hpos : (0 : ℝ) ≤ seqT n / 2 := by positivity
    rw [abs_of_nonneg hpos]
  have hblend : ∀ (w : ℂ) (_ : ‖w‖ ≤ 1),
      ‖((((1 - seqT n : ℝ))) : ℂ) * w + ((((seqT n / 2 : ℝ))) : ℂ)‖ < 1 := by
    intro w hw
    calc ‖((((1 - seqT n : ℝ))) : ℂ) * w + ((((seqT n / 2 : ℝ))) : ℂ)‖
        ≤ ‖((((1 - seqT n : ℝ))) : ℂ) * w‖
          + ‖((((seqT n / 2 : ℝ))) : ℂ)‖ := norm_add_le _ _
      _ = (1 - seqT n) * ‖w‖ + seqT n / 2 := by
          rw [norm_mul, hn1, hn2]
      _ ≤ (1 - seqT n) * 1 + seqT n / 2 := by
          have hmul : (1 - seqT n) * ‖w‖ ≤ (1 - seqT n) * 1 :=
            mul_le_mul_of_nonneg_left hw h1t_nonneg
          linarith
      _ < 1 := by linarith
  have hw0 : ‖blendSeq z0 n‖ < 1 := by
    unfold blendSeq
    exact hblend z0 hz0
  have heq1 : (1 : ℂ) - blendSeq z0 n
      = (((1 - seqT n : ℝ)) : ℂ) * ((1 : ℂ) - z0)
        + ((((seqT n / 2 : ℝ))) : ℂ) := by
    unfold blendSeq
    have hab : ((((1 - seqT n : ℝ))) : ℂ)
        + 2 * (((seqT n / 2 : ℝ)) : ℂ) = 1 := by
      have hreal : (1 - seqT n) + 2 * (seqT n / 2) = (1 : ℝ) := by ring
      have hcast : ((((1 - seqT n) + 2 * (seqT n / 2) : ℝ)) : ℂ)
          = (((1 : ℝ)) : ℂ) := by rw [hreal]
      have hexpand : ((((1 - seqT n) + 2 * (seqT n / 2) : ℝ)) : ℂ)
          = ((((1 - seqT n : ℝ))) : ℂ)
            + 2 * (((seqT n / 2 : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hexpand] at hcast
      simpa using hcast
    have hring : ∀ (a b z0 : ℂ), a + 2 * b = 1 →
        (1 - (a * z0 + b) = a * (1 - z0) + b) := by
      intro a b z0 hab2
      linear_combination -hab2
    exact hring _ _ _ hab
  have hw1 : ‖(1 : ℂ) - blendSeq z0 n‖ < 1 := by
    rw [heq1]
    exact hblend ((1 : ℂ) - z0) hz1
  constructor
  · rw [Metric.mem_ball, dist_eq_norm]
    have hsub : blendSeq z0 n - 0 = blendSeq z0 n := sub_zero _
    rw [hsub]
    exact hw0
  · rw [Metric.mem_ball, dist_eq_norm]
    have hrev : ‖blendSeq z0 n - 1‖ = ‖(1 : ℂ) - blendSeq z0 n‖ :=
      norm_sub_rev _ _
    rw [hrev]
    exact hw1

private lemma tendsto_blendSeq (z0 : ℂ) :
    Tendsto (blendSeq z0) atTop (𝓝 z0) := by
  have hmul : Tendsto (fun n : ℕ => seqU n * ((1 / 2 : ℂ) - z0)) atTop (𝓝 0) := by
    have h1 := tendsto_seqU
    have h2 : Tendsto (fun _ : ℕ => ((1 / 2 : ℂ) - z0)) atTop
        (𝓝 ((1 / 2 : ℂ) - z0)) := tendsto_const_nhds
    have hprod := h1.mul h2
    have h00 : (0 : ℂ) * ((1 / 2 : ℂ) - z0) = 0 := zero_mul _
    rw [h00] at hprod
    exact hprod
  have hadd : Tendsto (fun n : ℕ => z0 + seqU n * ((1 / 2 : ℂ) - z0)) atTop
      (𝓝 z0) := by
    have h1 : Tendsto (fun _ : ℕ => z0) atTop (𝓝 z0) := tendsto_const_nhds
    have hsum := h1.add hmul
    have hzz : z0 + (0 : ℂ) = z0 := add_zero _
    rw [hzz] at hsum
    exact hsum
  have hfun : blendSeq z0
      = (fun n : ℕ => z0 + seqU n * ((1 / 2 : ℂ) - z0)) := by
    funext n
    unfold blendSeq seqU
    push_cast
    ring
  rw [hfun]
  exact hadd

private lemma tendsto_one_sub_blendSeq (z0 : ℂ) :
    Tendsto (fun n : ℕ => (1 : ℂ) - blendSeq z0 n) atTop
      (𝓝 ((1 : ℂ) - z0)) := by
  have h1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
  exact h1.sub (tendsto_blendSeq z0)

private lemma blendSeq_mem_closedBall {z0 : ℂ} (hz : z0 ∈ closedLens)
    (n : ℕ) : blendSeq z0 n ∈ Metric.closedBall (0 : ℂ) 1 :=
  Metric.ball_subset_closedBall (blendSeq_mem_openLens hz n).1

private lemma one_sub_blendSeq_mem_closedBall {z0 : ℂ} (hz : z0 ∈ closedLens)
    (n : ℕ) : (1 : ℂ) - blendSeq z0 n ∈ Metric.closedBall (0 : ℂ) 1 := by
  have hmem := blendSeq_mem_openLens hz n
  have h1 : blendSeq z0 n ∈ Metric.ball (1 : ℂ) 1 := hmem.2
  have hdist : dist (blendSeq z0 n) (1 : ℂ) < 1 := Metric.mem_ball.mp h1
  rw [dist_eq_norm] at hdist
  have hnorm : ‖(1 : ℂ) - blendSeq z0 n‖ ≤ 1 := by
    have hrev : ‖(1 : ℂ) - blendSeq z0 n‖ = ‖blendSeq z0 n - 1‖ :=
      norm_sub_rev _ _
    rw [hrev]
    exact le_of_lt hdist
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : ((1 : ℂ) - blendSeq z0 n) - 0 = (1 : ℂ) - blendSeq z0 n :=
    sub_zero _
  rw [hsub]
  exact hnorm

private lemma spenceFun_eq_pi_sq_on_closedLens {z0 : ℂ} (hz : z0 ∈ closedLens)
    (hz0ne : z0 ≠ 0) (hz1ne : (1 : ℂ) - z0 ≠ 0) :
    spenceFun z0 = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
  have hz0Ball : z0 ∈ Metric.closedBall (0 : ℂ) 1 := hz.1
  have hz1Ball : (1 : ℂ) - z0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    have hle : ‖(1 : ℂ) - z0‖ ≤ 1 := norm_one_sub_le_one_of_mem_closedLens hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : ((1 : ℂ) - z0) - 0 = (1 : ℂ) - z0 := sub_zero _
    rw [hsub]
    exact hle
  have hcont0 : ContinuousWithinAt cLi2 (Metric.closedBall (0 : ℂ) 1) z0 :=
    continuousOn_cLi2.continuousWithinAt hz0Ball
  have hcont1 : ContinuousWithinAt cLi2 (Metric.closedBall (0 : ℂ) 1)
      ((1 : ℂ) - z0) :=
    continuousOn_cLi2.continuousWithinAt hz1Ball
  have hblend_within : Tendsto (blendSeq z0) atTop
      (𝓝[Metric.closedBall (0 : ℂ) 1] z0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_blendSeq z0)
      (Eventually.of_forall (blendSeq_mem_closedBall hz))
  have h1blend_within : Tendsto (fun n : ℕ => (1 : ℂ) - blendSeq z0 n) atTop
      (𝓝[Metric.closedBall (0 : ℂ) 1] ((1 : ℂ) - z0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_one_sub_blendSeq z0)
      (Eventually.of_forall (one_sub_blendSeq_mem_closedBall hz))
  have hL0 : Tendsto (fun n : ℕ => cLi2 (blendSeq z0 n)) atTop
      (𝓝 (cLi2 z0)) := by
    have hcomp : Tendsto (cLi2 ∘ blendSeq z0) atTop (𝓝 (cLi2 z0)) :=
      hcont0.tendsto.comp hblend_within
    have hfun : (cLi2 ∘ blendSeq z0)
        = (fun n : ℕ => cLi2 (blendSeq z0 n)) := rfl
    rw [hfun] at hcomp
    exact hcomp
  have hL1 : Tendsto (fun n : ℕ => cLi2 ((1 : ℂ) - blendSeq z0 n)) atTop
      (𝓝 (cLi2 ((1 : ℂ) - z0))) := by
    have hcomp : Tendsto (cLi2 ∘ (fun n : ℕ => (1 : ℂ) - blendSeq z0 n)) atTop
        (𝓝 (cLi2 ((1 : ℂ) - z0))) :=
      hcont1.tendsto.comp h1blend_within
    have hfun : (cLi2 ∘ (fun n : ℕ => (1 : ℂ) - blendSeq z0 n))
        = (fun n : ℕ => cLi2 ((1 : ℂ) - blendSeq z0 n)) := rfl
    rw [hfun] at hcomp
    exact hcomp
  have hslit0 : z0 ∈ Complex.slitPlane :=
    mem_slitPlane_of_mem_closedLens hz hz0ne
  have hslit1 : (1 : ℂ) - z0 ∈ Complex.slitPlane :=
    one_sub_mem_slitPlane_of_mem_closedLens hz hz1ne
  have hlog0 : Tendsto (fun n : ℕ => Complex.log (blendSeq z0 n)) atTop
      (𝓝 (Complex.log z0)) :=
    (tendsto_blendSeq z0).clog hslit0
  have hlog1 : Tendsto (fun n : ℕ => Complex.log ((1 : ℂ) - blendSeq z0 n))
      atTop (𝓝 (Complex.log ((1 : ℂ) - z0))) :=
    (tendsto_one_sub_blendSeq z0).clog hslit1
  have hprod : Tendsto (fun n : ℕ => Complex.log (blendSeq z0 n)
      * Complex.log ((1 : ℂ) - blendSeq z0 n)) atTop
      (𝓝 (Complex.log z0 * Complex.log ((1 : ℂ) - z0))) :=
    hlog0.mul hlog1
  have hlim : Tendsto (fun n : ℕ => spenceFun (blendSeq z0 n)) atTop
      (𝓝 (spenceFun z0)) := by
    have hadd := hL0.add hL1
    have hall := hadd.add hprod
    have hfun : (fun n : ℕ => spenceFun (blendSeq z0 n))
        = (fun n : ℕ => (cLi2 (blendSeq z0 n)
          + cLi2 ((1 : ℂ) - blendSeq z0 n)
          + Complex.log (blendSeq z0 n)
            * Complex.log ((1 : ℂ) - blendSeq z0 n))) := rfl
    have hval : spenceFun z0
        = (cLi2 z0 + cLi2 ((1 : ℂ) - z0)
          + Complex.log z0 * Complex.log ((1 : ℂ) - z0)) := rfl
    rw [hfun, hval]
    exact hall
  have hfunC : (fun n : ℕ => spenceFun (blendSeq z0 n))
      = fun _ => (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
    funext n
    exact spenceFun_eq_pi_sq_on_openLens _ (blendSeq_mem_openLens hz n)
  have hconst : Tendsto (fun n : ℕ => spenceFun (blendSeq z0 n)) atTop
      (𝓝 (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) := by
    rw [hfunC]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst

private lemma spence_identity {z w : ℂ} (hzw : z + w = 1)
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz0 : z ≠ 0) (hw0 : w ≠ 0) :
    cLi2 z + cLi2 w
      = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) - Complex.log z * Complex.log w := by
  have h1z : w = (1 : ℂ) - z := by linear_combination hzw
  have hzBall : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : z - 0 = z := sub_zero _
    rw [hsub]
    exact hz
  have hwBall : z ∈ Metric.closedBall (1 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : z - 1 = -w := by linear_combination hzw
    rw [heq, norm_neg]
    exact hw
  have hzLens : z ∈ closedLens := ⟨hzBall, hwBall⟩
  have h1ne : (1 : ℂ) - z ≠ 0 := h1z ▸ hw0
  have hsp := spenceFun_eq_pi_sq_on_closedLens hzLens hz0 h1ne
  have hsp2 : cLi2 z + cLi2 ((1 : ℂ) - z)
      + Complex.log z * Complex.log ((1 : ℂ) - z)
      = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := hsp
  rw [← h1z] at hsp2
  linear_combination hsp2

/-- **Entry 24 of Chapter 9 of Ramanujan's notebooks.** Let $x, y \in [0, 1]$ and
$\theta, \varphi \in (-\pi, \pi]$ satisfy $x e^{i\theta} + y e^{i\varphi} = 1$. Write
$\ell(t) = \log t$ for $0 < t \le 1$ and $\ell(0) = 0$. Then the four series
$\sum_{k \ge 1} \frac{x^k \cos k\theta}{k^2}$, $\sum_{k \ge 1} \frac{y^k \cos k\varphi}{k^2}$,
$\sum_{k \ge 1} \frac{x^k \sin k\theta}{k^2}$ and $\sum_{k \ge 1} \frac{y^k \sin k\varphi}{k^2}$
converge absolutely, and

$$
\sum_{k \ge 1} \frac{x^k \cos k\theta}{k^2} + \sum_{k \ge 1} \frac{y^k \cos k\varphi}{k^2} =
\frac{\pi^2}{6} - \ell(x) \ell(y) + \theta \varphi,
$$

$$
\sum_{k \ge 1} \frac{x^k \sin k\theta}{k^2} + \sum_{k \ge 1} \frac{y^k \sin k\varphi}{k^2} =
-\varphi \, \ell(x) - \theta \, \ell(y).
$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry24_dougall (x y theta phi : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (htheta : -Real.pi < theta ∧ theta ≤ Real.pi)
    (hphi : -Real.pi < phi ∧ phi ≤ Real.pi)
    (hxy : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) = 1) :
    Summable (chapter9DilogCosTerm x theta) ∧
      Summable (chapter9DilogCosTerm y phi) ∧
      Summable (chapter9DilogSinTerm x theta) ∧
      Summable (chapter9DilogSinTerm y phi) ∧
      (∑' j : ℕ, chapter9DilogCosTerm x theta j) +
          ∑' j : ℕ, chapter9DilogCosTerm y phi j =
        Real.pi ^ 2 / 6 - chapter9BoundaryLog x * chapter9BoundaryLog y +
          theta * phi ∧
      (∑' j : ℕ, chapter9DilogSinTerm x theta j) +
          ∑' j : ℕ, chapter9DilogSinTerm y phi j =
        -phi * chapter9BoundaryLog x - theta * chapter9BoundaryLog y := by
  have hcosx := summable_dilogCosTerm x theta hx.1 hx.2
  have hcosy := summable_dilogCosTerm y phi hy.1 hy.2
  have hsinx := summable_dilogSinTerm x theta hx.1 hx.2
  have hsiny := summable_dilogSinTerm y phi hy.1 hy.2
  have key : ((∑' j : ℕ, chapter9DilogCosTerm x theta j) +
          ∑' j : ℕ, chapter9DilogCosTerm y phi j =
        Real.pi ^ 2 / 6 - chapter9BoundaryLog x * chapter9BoundaryLog y +
          theta * phi) ∧
      ((∑' j : ℕ, chapter9DilogSinTerm x theta j) +
          ∑' j : ℕ, chapter9DilogSinTerm y phi j =
        -phi * chapter9BoundaryLog x - theta * chapter9BoundaryLog y) := by
    by_cases hx0 : x = 0
    · subst hx0
      simp only [Complex.ofReal_zero, zero_mul, zero_add] at hxy
      obtain ⟨hy1, hphi0⟩ := edge_of_rho_zero hy hphi hxy
      subst hy1
      subst hphi0
      constructor
      · rw [tsum_dilogCos_zero, zero_add, hasSum_dilogCos_one_zero.tsum_eq,
          boundaryLog_zero, boundaryLog_one]
        simp
      · rw [tsum_dilogSin_zero, tsum_dilogSin_one_zero, boundaryLog_zero,
          boundaryLog_one]
        simp
    · by_cases hy0 : y = 0
      · subst hy0
        simp only [Complex.ofReal_zero, zero_mul, add_zero] at hxy
        obtain ⟨hx1, htheta0⟩ := edge_of_rho_zero hx htheta hxy
        subst hx1
        subst htheta0
        constructor
        · rw [hasSum_dilogCos_one_zero.tsum_eq, tsum_dilogCos_zero, add_zero,
            boundaryLog_one, boundaryLog_zero]
          simp
        · rw [tsum_dilogSin_one_zero, tsum_dilogSin_zero, boundaryLog_one,
            boundaryLog_zero]
          simp
      · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
        have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
        have hznorm : ‖((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))‖ ≤ 1 := by
          rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hx.1]
          exact hx.2
        have hwnorm : ‖((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))‖ ≤ 1 := by
          rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hy.1]
          exact hy.2
        have hXsumm := summable_cLi2
          (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) hznorm
        have hYsumm := summable_cLi2
          (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) hwnorm
        have hXre : (∑' j : ℕ, (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (j + 1) /
            ((((j + 1 : ℕ)) : ℂ) ^ 2)).re
            = ∑' j : ℕ, chapter9DilogCosTerm x theta j := by
          rw [Complex.re_tsum hXsumm]
          refine tsum_congr fun j => ?_
          exact cLi2_cos x theta j
        have hYre : (∑' j : ℕ, (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) ^ (j + 1) /
            ((((j + 1 : ℕ)) : ℂ) ^ 2)).re
            = ∑' j : ℕ, chapter9DilogCosTerm y phi j := by
          rw [Complex.re_tsum hYsumm]
          refine tsum_congr fun j => ?_
          exact cLi2_cos y phi j
        have hXim : (∑' j : ℕ, (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (j + 1) /
            ((((j + 1 : ℕ)) : ℂ) ^ 2)).im
            = ∑' j : ℕ, chapter9DilogSinTerm x theta j := by
          rw [Complex.im_tsum hXsumm]
          refine tsum_congr fun j => ?_
          exact cLi2_sin x theta j
        have hYim : (∑' j : ℕ, (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) ^ (j + 1) /
            ((((j + 1 : ℕ)) : ℂ) ^ 2)).im
            = ∑' j : ℕ, chapter9DilogSinTerm y phi j := by
          rw [Complex.im_tsum hYsumm]
          refine tsum_congr fun j => ?_
          exact cLi2_sin y phi j
        have hlogx : Complex.log (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ)))
            = (((Real.log x : ℝ)) : ℂ) + ((theta : ℝ) : ℂ) * Complex.I :=
          log_ofReal_mul_exp_I x theta hxpos ⟨htheta.1, htheta.2⟩
        have hlogy : Complex.log (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ)))
            = (((Real.log y : ℝ)) : ℂ) + ((phi : ℝ) : ℂ) * Complex.I :=
          log_ofReal_mul_exp_I y phi hypos ⟨hphi.1, hphi.2⟩
        have hBlogx : chapter9BoundaryLog x = Real.log x := by
          simp [chapter9BoundaryLog, hx0]
        have hBlogy : chapter9BoundaryLog y = Real.log y := by
          simp [chapter9BoundaryLog, hy0]
        have hz0 : (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ≠ 0 := by
          have hnorm_eq : ‖(((x : ℝ) : ℂ)
              * Complex.exp (Complex.I * (theta : ℂ)))‖ = x := by
            rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hx.1]
          have hpos : (0 : ℝ) < ‖(((x : ℝ) : ℂ)
              * Complex.exp (Complex.I * (theta : ℂ)))‖ := by
            rw [hnorm_eq]
            exact hxpos
          exact norm_ne_zero_iff.mp (ne_of_gt hpos)
        have hw0 : (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) ≠ 0 := by
          have hnorm_eq : ‖(((y : ℝ) : ℂ)
              * Complex.exp (Complex.I * (phi : ℂ)))‖ = y := by
            rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hy.1]
          have hpos : (0 : ℝ) < ‖(((y : ℝ) : ℂ)
              * Complex.exp (Complex.I * (phi : ℂ)))‖ := by
            rw [hnorm_eq]
            exact hypos
          exact norm_ne_zero_iff.mp (ne_of_gt hpos)
        have hzw : (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ)))
            + (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) = 1 := hxy
        have hsp := spence_identity hzw hznorm hwnorm hz0 hw0
        have spence : (∑' j : ℕ, (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (j + 1) /
              ((((j + 1 : ℕ)) : ℂ) ^ 2)) +
            (∑' j : ℕ, (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) ^ (j + 1) /
              ((((j + 1 : ℕ)) : ℂ) ^ 2))
            = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) -
              Complex.log (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) *
              Complex.log (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) :=
          hsp
        have hre := congrArg Complex.re spence
        have him := congrArg Complex.im spence
        rw [Complex.add_re, hXre, hYre, hlogx, hlogy] at hre
        rw [Complex.add_im, hXim, hYim, hlogx, hlogy] at him
        simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, mul_one, sub_zero, add_zero, zero_add] at hre
        simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.add_im,
          Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_one, mul_zero, add_zero, zero_add] at him
        rw [hBlogx, hBlogy]
        constructor
        · linarith [hre]
        · linarith [him]
  exact ⟨hcosx, hcosy, hsinx, hsiny, key.1, key.2⟩

end
end Entry24Dougall
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
