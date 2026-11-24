/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half.lean`
and
`P2M/Sol/S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open scoped Real


namespace GluePNearZero

private noncomputable def eA (t : ℝ) : ℝ := Real.exp (-t)
private noncomputable def eB (t : ℝ) : ℝ := Real.exp (t / 2)

private lemma eA_pos (t : ℝ) : 0 < eA t := Real.exp_pos _
private lemma eB_pos (t : ℝ) : 0 < eB t := Real.exp_pos _
private lemma eA_le_one {t : ℝ} (ht : 0 ≤ t) : eA t ≤ 1 := by
  unfold eA; exact Real.exp_le_one_iff.mpr (by linarith)
private lemma eA_zero : eA 0 = 1 := by simp [eA]
private lemma eB_sq (t : ℝ) : eB t ^ 2 = Real.exp t := by
  unfold eB; rw [← Real.exp_nat_mul]; congr 1; ring
private lemma eA_mul_eB_sq (t : ℝ) : eA t * eB t ^ 2 = 1 := by
  rw [eB_sq]; unfold eA; rw [← Real.exp_add]; simp

private lemma eA_hasDerivAt (t : ℝ) : HasDerivAt eA (-(eA t)) t := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * (-1)) t := (hasDerivAt_neg
    t).exp
  unfold eA; simpa using h
private lemma eB_hasDerivAt (t : ℝ) : HasDerivAt eB (eB t / 2) t := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (x / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    have h0 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const (2 : ℝ)
    exact h0.exp
  unfold eB; convert h using 1; ring

private noncomputable def Gf (f : ℝ → ℂ) (t : ℝ) : ℂ := (eB t : ℂ) * f (eA t)

private noncomputable def Hf (f : ℝ → ℂ) (t : ℝ) : ℂ := (eA t : ℂ) * (eB t : ℂ) * deriv f (eA t)
private noncomputable def vp (l : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ := (1 / 2 + l) * Gf f t - Hf f t
private noncomputable def vm (l : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ := (1 / 2 - l) * Gf f t - Hf f t
private noncomputable def sfun (ν l : ℂ) (k : ℝ) (t : ℝ) : ℂ :=
  ν ^ 2 - l ^ 2 + 4 * (π : ℂ) ^ 2 * ((eA t : ℝ) : ℂ) ^ 2 - 2 * (π : ℂ) * (k : ℂ) * ((eA t : ℝ) : ℂ)

private lemma vp_sub_vm (l : ℂ) (f : ℝ → ℂ) (t : ℝ) : vp l f t - vm l f t = 2 * l * Gf f t := by
  unfold vp vm; ring

section derivs

variable (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f)
  (Set.Ioi 0))
include hf hf'

omit hf' in
private lemma Gf_hasDerivAt (t : ℝ) :
    HasDerivAt (Gf f) (((eB t / 2 : ℝ) : ℂ) * f (eA t) + (eB t : ℂ) * (((-(eA t) : ℝ) : ℂ) * deriv
      f (eA t))) t := by
  have hy : eA t ∈ Set.Ioi (0 : ℝ) := eA_pos t
  have h1 : HasDerivAt (fun x : ℝ => ((eB x : ℝ) : ℂ)) ((eB t / 2 : ℝ) : ℂ) t := (eB_hasDerivAt
    t).ofReal_comp
  have hfy : HasDerivAt f (deriv f (eA t)) (eA t) :=
    ((hf.differentiableAt (Ioi_mem_nhds (eA_pos t))).hasDerivAt)
  have h2 : HasDerivAt (fun x : ℝ => f (eA x)) ((-(eA t)) • deriv f (eA t)) t := hfy.scomp t
    (eA_hasDerivAt t)
  have h3 := h1.mul h2
  unfold Gf
  convert h3 using 1

omit hf in
private lemma Hf_hasDerivAt (t : ℝ) :
    HasDerivAt (Hf f)
      ((((-(eA t) : ℝ) : ℂ) * (eB t : ℂ) + (eA t : ℂ) * ((eB t / 2 : ℝ) : ℂ)) * deriv f (eA t)
        + (eA t : ℂ) * (eB t : ℂ) * (((-(eA t) : ℝ) : ℂ) * deriv (deriv f) (eA t))) t := by
  have h1 : HasDerivAt (fun x : ℝ => ((eA x : ℝ) : ℂ)) ((-(eA t) : ℝ) : ℂ) t := (eA_hasDerivAt
    t).ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => ((eB x : ℝ) : ℂ)) ((eB t / 2 : ℝ) : ℂ) t := (eB_hasDerivAt
    t).ofReal_comp
  have hfy : HasDerivAt (deriv f) (deriv (deriv f) (eA t)) (eA t) :=
    ((hf'.differentiableAt (Ioi_mem_nhds (eA_pos t))).hasDerivAt)
  have h3 : HasDerivAt (fun x : ℝ => deriv f (eA x)) ((-(eA t)) • deriv (deriv f) (eA t)) t :=
    hfy.scomp t (eA_hasDerivAt t)
  have h4 := (h1.mul h2).mul h3
  unfold Hf
  convert h4 using 1

variable (ν : ℂ) (k : ℝ)
variable (hfeq : ∀ y : ℝ, 0 < y →
    (y : ℂ) ^ 2 * deriv (deriv f) y
      + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
include hfeq

private lemma vp_hasDerivAt (l : ℂ) (t : ℝ) :
    HasDerivAt (vp l f) (l * vp l f t + sfun ν l k t * Gf f t) t := by
  have hG := Gf_hasDerivAt f hf t
  have hH := Hf_hasDerivAt f hf' t
  have h := (hG.const_mul (1 / 2 + l)).sub hH
  have hode := hfeq (eA t) (eA_pos t)
  refine (h.congr_deriv ?_)
  unfold vp Gf Hf sfun
  push_cast
  linear_combination ((eB t : ℝ) : ℂ) * hode

private lemma vm_hasDerivAt (l : ℂ) (t : ℝ) :
    HasDerivAt (vm l f) (-l * vm l f t + sfun ν l k t * Gf f t) t := by
  have hG := Gf_hasDerivAt f hf t
  have hH := Hf_hasDerivAt f hf' t
  have h := (hG.const_mul (1 / 2 - l)).sub hH
  have hode := hfeq (eA t) (eA_pos t)
  refine (h.congr_deriv ?_)
  unfold vm Gf Hf sfun
  push_cast
  linear_combination ((eB t : ℝ) : ℂ) * hode

end derivs

private noncomputable def nsq (v : ℝ → ℂ) (t : ℝ) : ℝ := (v t).re * (v t).re + (v t).im * (v t).im

private lemma nsq_eq (v : ℝ → ℂ) (t : ℝ) : nsq v t = ‖v t‖ ^ 2 := by
  unfold nsq; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

private lemma nsq_hasDerivAt {v : ℝ → ℂ} {v' : ℂ} {t : ℝ} (hv : HasDerivAt v v' t) :
    HasDerivAt (nsq v) (2 * ((v t).re * v'.re + (v t).im * v'.im)) t := by
  have hre : HasDerivAt (fun x => (v x).re) v'.re t := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hv
    simp at this
    exact this
  have him : HasDerivAt (fun x => (v x).im) v'.im t := by
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hv
    simp at this
    exact this
  have h := (hre.mul hre).add (him.mul him)
  unfold nsq
  convert h using 1
  ring

private lemma cross_le (v w : ℂ) : v.re * w.re + v.im * w.im ≤ ‖v‖ * ‖w‖ := by
  have h1 : v.re * w.re + v.im * w.im = ((starRingEnd ℂ) v * w).re := by
    simp [Complex.mul_re]
  have h2 : ((starRingEnd ℂ) v * w).re ≤ ‖(starRingEnd ℂ) v * w‖ := Complex.re_le_norm _
  rw [h1]; refine h2.trans (le_of_eq ?_); rw [norm_mul, Complex.norm_conj]

private lemma cross_decomp (v c w : ℂ) :
    v.re * (c * v + w).re + v.im * (c * v + w).im
      = c.re * (v.re * v.re + v.im * v.im) + (v.re * w.re + v.im * w.im) := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]; ring

private lemma rate_bound (p q g S m lre Li cp cm : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hg0 : 0 ≤ g) (hS
  : 0 ≤ S)
    (hSm : S ≤ m) (hLi : 0 ≤ Li) (hg : 2 * g ≤ Li * (p + q)) (hcp : cp ≤ p * (S * g)) (hcm : cm ≤
      q * (S * g)) :
    2 * (lre * (p * p) + cp) + 2 * ((-lre) * (q * q) + cm) ≤ (2 * |lre| + 2 * Li * m) * (p * p + q
      * q) := by
  have hl1 : lre ≤ |lre| := le_abs_self lre
  have hl2 : -lre ≤ |lre| := neg_le_abs lre
  have hpq : 0 ≤ p * p := mul_nonneg hp hp
  have hqq : 0 ≤ q * q := mul_nonneg hq hq

  have hSg : 0 ≤ S * g := mul_nonneg hS hg0
  have h1 : cp + cm ≤ S * g * (p + q) := by nlinarith
  have h2 : 2 * (S * g * (p + q)) ≤ S * (Li * (p + q)) * (p + q) := by
    have := mul_le_mul_of_nonneg_left hg (mul_nonneg hS (add_nonneg hp hq))
    nlinarith
  have h3 : S * (Li * (p + q)) * (p + q) ≤ S * Li * (2 * (p * p + q * q)) := by
    have hsq : (p + q) * (p + q) ≤ 2 * (p * p + q * q) := by nlinarith [mul_self_nonneg (p - q)]
    have hSL : 0 ≤ S * Li := mul_nonneg hS hLi
    nlinarith [mul_le_mul_of_nonneg_left hsq hSL]
  have h4 : S * Li * (2 * (p * p + q * q)) ≤ m * Li * (2 * (p * p + q * q)) := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSm hLi)
      (by positivity : (0:ℝ) ≤ 2 * (p * p + q * q))
    linarith
  have hdiag : 2 * (lre * (p * p)) + 2 * ((-lre) * (q * q)) ≤ 2 * |lre| * (p * p + q * q) := by
    nlinarith [mul_le_mul_of_nonneg_right hl1 hpq, mul_le_mul_of_nonneg_right hl2 hqq]
  nlinarith [h1, h2, h3, h4, hdiag]

section energy

variable (ν l : ℂ) (k : ℝ) (f : ℝ → ℂ)
variable (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
variable (hfeq : ∀ y : ℝ, 0 < y →
    (y : ℂ) ^ 2 * deriv (deriv f) y
      + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)

private noncomputable def Efun (t : ℝ) : ℝ := nsq (vp l f) t + nsq (vm l f) t

private lemma Efun_nonneg (t : ℝ) : 0 ≤ Efun l f t := by
  unfold Efun; rw [nsq_eq, nsq_eq]; positivity

private noncomputable def mfun (m₀ : ℝ) (t : ℝ) : ℝ := m₀ + 2 * π * |k| * eA t + 4 * π ^ 2 * (eA t
  * eA t)

private lemma norm_sfun_le (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) (t : ℝ) : ‖sfun ν l k t‖ ≤ mfun k
  m₀ t := by
  unfold sfun mfun
  have hA : 0 ≤ eA t := (eA_pos t).le
  have hpi : ‖(π : ℂ)‖ = π := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hk : ‖(k : ℂ)‖ = |k| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hAn : ‖((eA t : ℝ) : ℂ)‖ = eA t := by rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hA]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  calc ‖ν ^ 2 - l ^ 2 + 4 * (π : ℂ) ^ 2 * ((eA t : ℝ) : ℂ) ^ 2 - 2 * (π : ℂ) * (k : ℂ) * ((eA t :
    ℝ) : ℂ)‖
      ≤ ‖ν ^ 2 - l ^ 2 + 4 * (π : ℂ) ^ 2 * ((eA t : ℝ) : ℂ) ^ 2‖ + ‖2 * (π : ℂ) * (k : ℂ) * ((eA t
        : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ (‖ν ^ 2 - l ^ 2‖ + ‖4 * (π : ℂ) ^ 2 * ((eA t : ℝ) : ℂ) ^ 2‖) + ‖2 * (π : ℂ) * (k : ℂ) *
      ((eA t : ℝ) : ℂ)‖ := by
        gcongr; exact norm_add_le _ _
    _ = (‖ν ^ 2 - l ^ 2‖ + 4 * π ^ 2 * (eA t * eA t)) + 2 * π * |k| * eA t := by
        rw [norm_mul, norm_mul, norm_pow, norm_pow, h4, hpi, hAn, norm_mul, norm_mul, norm_mul,
          h2, hpi, hk, hAn]; ring
    _ ≤ (m₀ + 4 * π ^ 2 * (eA t * eA t)) + 2 * π * |k| * eA t := by gcongr
    _ = m₀ + 2 * π * |k| * eA t + 4 * π ^ 2 * (eA t * eA t) := by ring

private noncomputable def rate (m₀ : ℝ) (t : ℝ) : ℝ := 2 * |l.re| + 2 * ‖l‖⁻¹ * mfun k m₀ t

include hf hf' hfeq in
private lemma Efun_hasDerivAt_le (hl : l ≠ 0) (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) (t : ℝ) :
    ∃ E' : ℝ, HasDerivAt (Efun l f) E' t ∧ E' ≤ rate l k m₀ t * Efun l f t := by
  have hvp := vp_hasDerivAt f hf hf' ν k hfeq l t
  have hvm := vm_hasDerivAt f hf hf' ν k hfeq l t
  have hEp := nsq_hasDerivAt hvp
  have hEm := nsq_hasDerivAt hvm
  refine ⟨_, hEp.add hEm, ?_⟩

  set w := sfun ν l k t * Gf f t with hw
  have hdp := cross_decomp (vp l f t) l w
  have hdm := cross_decomp (vm l f t) (-l) w
  have hcp := cross_le (vp l f t) w
  have hcm := cross_le (vm l f t) w
  have hwn : ‖w‖ = ‖sfun ν l k t‖ * ‖Gf f t‖ := by rw [hw, norm_mul]
  have hS := norm_sfun_le ν l k m₀ hm₀ t
  have hS0 : 0 ≤ ‖sfun ν l k t‖ := norm_nonneg _
  have hLi : 0 ≤ ‖l‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hl0 : 0 < ‖l‖ := norm_pos_iff.mpr hl

  have hg : 2 * ‖Gf f t‖ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := by
    have h1 : ‖vp l f t - vm l f t‖ ≤ ‖vp l f t‖ + ‖vm l f t‖ := norm_sub_le _ _
    rw [vp_sub_vm, norm_mul, norm_mul] at h1
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at h1

    have h3 := mul_le_mul_of_nonneg_left h1 hLi
    calc 2 * ‖Gf f t‖ = ‖l‖⁻¹ * (2 * ‖l‖ * ‖Gf f t‖) := by field_simp
      _ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := h3
  have hmain := rate_bound ‖vp l f t‖ ‖vm l f t‖ ‖Gf f t‖ ‖sfun ν l k t‖ (mfun k m₀ t) l.re ‖l‖⁻¹
    ((vp l f t).re * w.re + (vp l f t).im * w.im) ((vm l f t).re * w.re + (vm l f t).im * w.im)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hS0 hS hLi hg (by rw [← hwn]; exact hcp) (by
      rw [← hwn]; exact hcm)

  have hnp : (vp l f t).re * (vp l f t).re + (vp l f t).im * (vp l f t).im = ‖vp l f t‖ * ‖vp l f
    t‖ := by
    have := nsq_eq (vp l f) t; unfold nsq at this; rw [this]; ring
  have hnm : (vm l f t).re * (vm l f t).re + (vm l f t).im * (vm l f t).im = ‖vm l f t‖ * ‖vm l f
    t‖ := by
    have := nsq_eq (vm l f) t; unfold nsq at this; rw [this]; ring
  have hEt : Efun l f t = ‖vp l f t‖ * ‖vp l f t‖ + ‖vm l f t‖ * ‖vm l f t‖ := by
    unfold Efun; rw [nsq_eq, nsq_eq]; ring
  rw [hEt]
  unfold rate
  simp only [Complex.neg_re] at hdm
  rw [hdp, hdm, hnp, hnm]
  linarith [hmain]

private noncomputable def Phi (m₀ : ℝ) (t : ℝ) : ℝ :=
  2 * |l.re| * t + 2 * ‖l‖⁻¹ * (m₀ * t + 2 * π * |k| * (1 - eA t) + 4 * π ^ 2 / 2 * (1 - eA t * eA
    t))

private lemma Phi_hasDerivAt (m₀ : ℝ) (t : ℝ) : HasDerivAt (Phi l k m₀) (rate l k m₀ t) t := by
  have hA := eA_hasDerivAt t
  have h1 : HasDerivAt (fun x : ℝ => 1 - eA x) (-(-(eA t))) t := hA.const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => 1 - eA x * eA x) (-((-(eA t)) * eA t + eA t * (-(eA t)))) t :=
    (hA.mul hA).const_sub 1
  have h3 : HasDerivAt (fun x : ℝ => m₀ * x) (m₀ * 1) t := (hasDerivAt_id t).const_mul m₀
  have h4 : HasDerivAt (fun x : ℝ => 2 * |l.re| * x) (2 * |l.re| * 1) t := (hasDerivAt_id
    t).const_mul _
  have h := h4.add ((((h3.add (h1.const_mul (2 * π * |k|))).add (h2.const_mul (4 * π ^ 2 /
    2)))).const_mul (2 * ‖l‖⁻¹))
  unfold Phi rate mfun
  convert h using 1
  ring

private lemma Phi_zero (m₀ : ℝ) : Phi l k m₀ 0 = 0 := by
  unfold Phi; rw [eA_zero]; ring

private lemma Phi_le (m₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Phi l k m₀ t ≤ (2 * |l.re| + 2 * ‖l‖⁻¹ * m₀) * t + 2 * ‖l‖⁻¹ * (2 * π * |k| + 4 * π ^ 2 / 2)
      := by
  unfold Phi
  have hA0 : 0 ≤ eA t := (eA_pos t).le
  have hA1 : eA t ≤ 1 := eA_le_one ht
  have hLi : 0 ≤ ‖l‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hk0 : 0 ≤ 2 * π * |k| := by positivity
  have hpi : 0 ≤ 4 * π ^ 2 / 2 := by positivity
  have e1 : 2 * π * |k| * (1 - eA t) ≤ 2 * π * |k| := by nlinarith
  have e2 : 4 * π ^ 2 / 2 * (1 - eA t * eA t) ≤ 4 * π ^ 2 / 2 := by nlinarith [mul_nonneg hA0 hA0]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add e1 e2) hLi]

include hf hf' hfeq in

private lemma Efun_le (hl : l ≠ 0) (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) {t : ℝ} (ht : 0 ≤ t) :
    Efun l f t ≤ Efun l f 0 * Real.exp (Phi l k m₀ t) := by

  set Z : ℝ → ℝ := fun x => Efun l f x * Real.exp (-(Phi l k m₀ x)) with hZdef
  have hZ : ∀ x : ℝ, ∃ Z' : ℝ, HasDerivAt Z Z' x ∧ Z' ≤ 0 := by
    intro x
    obtain ⟨E', hE', hle⟩ := Efun_hasDerivAt_le ν l k f hf hf' hfeq hl m₀ hm₀ x
    have hP : HasDerivAt (fun y => Real.exp (-(Phi l k m₀ y))) (Real.exp (-(Phi l k m₀ x)) *
      (-(rate l k m₀ x))) x :=
      ((Phi_hasDerivAt l k m₀ x).neg).exp
    refine ⟨_, hE'.mul hP, ?_⟩
    have hexp : 0 < Real.exp (-(Phi l k m₀ x)) := Real.exp_pos _
    have hE0 := Efun_nonneg l f x
    have : E' * Real.exp (-(Phi l k m₀ x)) + Efun l f x * (Real.exp (-(Phi l k m₀ x)) * -rate l k
      m₀ x)
        = Real.exp (-(Phi l k m₀ x)) * (E' - rate l k m₀ x * Efun l f x) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hexp.le (by linarith)
  have hcont : ContinuousOn Z (Set.Ici 0) := fun x _ => ((hZ
    x).choose_spec.1.continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ Z (interior (Set.Ici (0 : ℝ))) :=
    fun x _ => ((hZ x).choose_spec.1.differentiableAt).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)), deriv Z x ≤ 0 := by
    intro x _
    obtain ⟨Z', hZ', hle⟩ := hZ x
    rw [hZ'.deriv]; exact hle
  have hanti : AntitoneOn Z (Set.Ici 0) := antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff
    hderiv
  have h0 : Z t ≤ Z 0 := hanti Set.self_mem_Ici ht ht
  have hZ0 : Z 0 = Efun l f 0 := by simp [hZdef, Phi_zero]
  rw [hZ0] at h0

  have hZt : Z t = Efun l f t * Real.exp (-(Phi l k m₀ t)) := rfl
  rw [hZt] at h0
  have hpos : 0 < Real.exp (Phi l k m₀ t) := Real.exp_pos _
  have := mul_le_mul_of_nonneg_right h0 hpos.le
  rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this

include hf hf' hfeq in

private theorem engine (hl : l ≠ 0) (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀)
    (hρ : 2 * |l.re| + 2 * ‖l‖⁻¹ * m₀ < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ δ := by
  set ρ : ℝ := 2 * |l.re| + 2 * ‖l‖⁻¹ * m₀ with hρdef
  set K : ℝ := 2 * ‖l‖⁻¹ * (2 * π * |k| + 4 * π ^ 2 / 2) with hKdef
  have hLi : 0 ≤ ‖l‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  set Cst : ℝ := ‖l‖⁻¹ * ‖l‖⁻¹ / 2 * (Efun l f 0 * Real.exp K) with hCst
  have hCst0 : 0 ≤ Cst := by
    have := Efun_nonneg l f 0; have := Real.exp_pos K; positivity
  refine ⟨(1 - ρ) / 2, by linarith, Real.sqrt Cst, ?_⟩
  intro y hy hy1

  set t : ℝ := -Real.log y with htdef
  have ht : 0 ≤ t := by have := Real.log_nonpos hy.le hy1; linarith
  have hAt : eA t = y := by unfold eA; rw [htdef, neg_neg, Real.exp_log hy]

  have hG : Gf f t = ((eB t : ℝ) : ℂ) * f y := by unfold Gf; rw [hAt]
  have hGn : ‖Gf f t‖ = eB t * ‖f y‖ := by
    rw [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eB_pos t)]
  have hfy_sq : ‖f y‖ ^ 2 = y * ‖Gf f t‖ ^ 2 := by
    rw [hGn, mul_pow, ← hAt, ← mul_assoc, eA_mul_eB_sq, one_mul]

  have hE := Efun_le ν l k f hf hf' hfeq hl m₀ hm₀ ht
  have hgl : 2 * ‖Gf f t‖ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := by
    have h1 : ‖vp l f t - vm l f t‖ ≤ ‖vp l f t‖ + ‖vm l f t‖ := norm_sub_le _ _
    rw [vp_sub_vm, norm_mul, norm_mul] at h1
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hLi
    have hl0 : 0 < ‖l‖ := norm_pos_iff.mpr hl
    calc 2 * ‖Gf f t‖ = ‖l‖⁻¹ * (2 * ‖l‖ * ‖Gf f t‖) := by field_simp
      _ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := h3
  have hEt : Efun l f t = ‖vp l f t‖ ^ 2 + ‖vm l f t‖ ^ 2 := by unfold Efun; rw [nsq_eq, nsq_eq]
  have hGsq : ‖Gf f t‖ ^ 2 ≤ ‖l‖⁻¹ * ‖l‖⁻¹ / 2 * Efun l f t := by
    rw [hEt]
    have hp := norm_nonneg (vp l f t); have hq := norm_nonneg (vm l f t); have hg0 := norm_nonneg
      (Gf f t)
    have hsum : (‖vp l f t‖ + ‖vm l f t‖) ^ 2 ≤ 2 * (‖vp l f t‖ ^ 2 + ‖vm l f t‖ ^ 2) := by
      nlinarith [sq_nonneg (‖vp l f t‖ - ‖vm l f t‖)]
    have h4 : (2 * ‖Gf f t‖) ^ 2 ≤ (‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hgl 2
    have hLi2 : 0 ≤ ‖l‖⁻¹ * ‖l‖⁻¹ := mul_nonneg hLi hLi
    nlinarith [mul_le_mul_of_nonneg_left hsum hLi2]

  have hPhi := Phi_le l k m₀ ht
  have hexp : Real.exp (Phi l k m₀ t) ≤ Real.exp K * y ^ (-ρ) := by
    rw [Real.rpow_def_of_pos hy, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : K + Real.log y * -ρ = ρ * t + K := by rw [htdef]; ring
    rw [this]; exact hPhi
  have hE0 := Efun_nonneg l f 0

  have hsq : ‖f y‖ ^ 2 ≤ Cst * (y * y ^ (-ρ)) := by
    rw [hfy_sq, hCst]
    have hLi2 : 0 ≤ ‖l‖⁻¹ * ‖l‖⁻¹ / 2 := by positivity
    calc y * ‖Gf f t‖ ^ 2 ≤ y * (‖l‖⁻¹ * ‖l‖⁻¹ / 2 * Efun l f t) := by gcongr
      _ ≤ y * (‖l‖⁻¹ * ‖l‖⁻¹ / 2 * (Efun l f 0 * Real.exp (Phi l k m₀ t))) := by gcongr
      _ ≤ y * (‖l‖⁻¹ * ‖l‖⁻¹ / 2 * (Efun l f 0 * (Real.exp K * y ^ (-ρ)))) := by gcongr
      _ = ‖l‖⁻¹ * ‖l‖⁻¹ / 2 * (Efun l f 0 * Real.exp K) * (y * y ^ (-ρ)) := by ring
  have hyρ : y * y ^ (-ρ) = (y ^ ((1 - ρ) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    have h1 : y * y ^ (-ρ) = y ^ (1 + -ρ) := by rw [Real.rpow_add hy, Real.rpow_one]
    rw [h1]
    congr 1; push_cast; ring
  rw [hyρ] at hsq
  have hrhs : 0 ≤ Real.sqrt Cst * y ^ ((1 - ρ) / 2) := by positivity
  have hsq' : ‖f y‖ ^ 2 ≤ (Real.sqrt Cst * y ^ ((1 - ρ) / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hCst0]; exact hsq
  have := abs_le_of_sq_le_sq hsq' hrhs
  rwa [abs_of_nonneg (norm_nonneg _)] at this

end energy

end GluePNearZero

open GluePNearZero in
/-- Every solution of the Whittaker-type equation
`y² f'' + (1/4 - ν² + 2πky - 4π²y²) f = 0` on `(0, ∞)` with `|Re ν| < 1/2`
satisfies a power bound `‖f y‖ ≤ C y^δ` for some `δ > 0` and all `0 < y ≤ 1`. -/
theorem LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half
    (ν : ℂ) (hre : |ν.re| < 1 / 2) (k : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) *
              f y = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ δ := by
  by_cases hν : ν = 0
  ·
    subst hν
    have hl : (((1 / 8 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by norm_num)
    have hnorm : ‖(((1 / 8 : ℝ) : ℂ))‖ = 1 / 8 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have hm : ‖(0 : ℂ) ^ 2 - (((1 / 8 : ℝ) : ℂ)) ^ 2‖ ≤ 1 / 64 := by
      rw [show (0 : ℂ) ^ 2 - (((1 / 8 : ℝ) : ℂ)) ^ 2 = -((((1 / 8 : ℝ) : ℂ)) ^ 2) by ring,
        norm_neg, norm_pow, hnorm]
      norm_num
    refine engine 0 (((1 / 8 : ℝ) : ℂ)) k f hf hf' hfeq hl (1 / 64) hm ?_
    rw [hnorm, Complex.ofReal_re, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
    norm_num
  ·
    have hm : ‖ν ^ 2 - ν ^ 2‖ ≤ 0 := by simp
    refine engine ν ν k f hf hf' hfeq hν 0 hm ?_
    rw [mul_zero, add_zero]
    linarith
