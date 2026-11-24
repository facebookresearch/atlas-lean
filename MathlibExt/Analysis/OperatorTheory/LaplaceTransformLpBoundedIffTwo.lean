/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_31.lean` (openbmb/ma-proofbench, commit 31bab4c).
Copyright (c) 2026 OpenBMB. Licensed under the MIT License.
Authors: L. Pu et al.

The statement of the main theorem is adapted from the benchmark. The proof is original.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Prod
import MathlibExt.Probability.Distributions.GammaLIntegral

/-!
# Boundedness of the Laplace transform on the positive half-line

The Laplace transform is bounded from real `L^p` to itself exactly when `p = 2`.
For the square-integrable case, weighted Cauchy–Schwarz with weight `x ^ (-1 / 2)`
gives the bound `Γ(1 / 2)`. Testing on indicators of `(0, t]` forces the exponent.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExt.Analysis.OperatorTheory.LaplaceTransformLpBoundedIffTwoWanted

private noncomputable abbrev ray := volume.restrict (Ioi (0 : ℝ))

private noncomputable abbrev transform (f : ℝ → ℝ) (s : ℝ) :=
  ∫ x, Real.exp (-x * s) * f x ∂ray

private noncomputable abbrev kernel (s x : ℝ) := ENNReal.ofReal (Real.exp (-x * s))

private noncomputable abbrev weight (x : ℝ) := ENNReal.ofReal (x ^ (-(1 / 2) : ℝ))

private noncomputable abbrev gammaHalf := ENNReal.ofReal (Real.Gamma (1 / 2))

private lemma weight_pos {x : ℝ} (hx : 0 < x) : 0 < weight x :=
  ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hx _)

-- The weight is an eigenfunction of the positive kernel.
private lemma weighted_row {s : ℝ} (hs : 0 < s) :
    ∫⁻ x, kernel s x * weight x ∂ray = gammaHalf * weight s := by
  have h := ProbabilityTheory.lintegral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (by norm_num) hs
  have eqn : (fun x : ℝ => ENNReal.ofReal
      (if 0 < x then x ^ (1 / 2 - 1 : ℝ) * Real.exp (-(s * x)) else 0)) =
      (Ioi 0).indicator (fun x => kernel s x * weight x) := by
    funext x
    by_cases hx : 0 < x
    · simp only [ite_eq_left hx, indicator_of_mem (mem_Ioi.mpr hx), kernel, weight]
      rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, mul_comm, mul_comm s x, ← neg_mul,
        ENNReal.ofReal_mul (Real.exp_pos _).le]
    · simp [hx]
  rw [eqn, lintegral_indicator measurableSet_Ioi] at h
  rw [h, gammaHalf, weight, Real.rpow_neg hs.le, div_eq_mul_inv,
    ENNReal.ofReal_mul (Real.Gamma_pos_of_pos (by norm_num)).le]

private lemma norm_transform_sq_le (f : ℝ → ℝ) (hf : AEStronglyMeasurable f ray)
    {s : ℝ} (hs : 0 < s) :
    ‖transform f s‖ₑ ^ 2 ≤ (gammaHalf * weight s) *
      ∫⁻ x, kernel s x * (‖f x‖ₑ ^ 2 / weight x) ∂ray := by
  let A x := kernel s x * weight x
  let B x := kernel s x * (‖f x‖ₑ ^ 2 / weight x)
  have hAB : ∀ᵐ x ∂ray, A x * B x = (kernel s x * ‖f x‖ₑ) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    dsimp only [A, B]
    rw [mul_mul_mul_comm, ENNReal.mul_div_cancel (weight_pos hx).ne' ENNReal.ofReal_ne_top,
      mul_pow, sq, sq]
  have hCS := ENNReal.lintegral_mul_norm_pow_le (μ := ray) (f := A) (g := B)
    (by dsimp [A, kernel, weight]; fun_prop)
    (by dsimp [B, kernel, weight]; fun_prop)
    (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hbound : ‖transform f s‖ₑ ≤ ((∫⁻ x, A x ∂ray) * ∫⁻ x, B x ∂ray) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    refine (eNorm_integral_le_lintegral_eNorm _).trans (le_trans ?_ hCS)
    apply lintegral_mono_ae
    filter_upwards [hAB] with x hx
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hx, ← ENNReal.rpow_two,
      ← ENNReal.rpow_mul]
    norm_num [Real.eNorm_eq_ofReal (Real.exp_pos _).le, kernel]
  have h := pow_le_pow_left' hbound 2
  simpa only [← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    one_div_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_one, A, B, weighted_row hs] using h

-- Tonelli turns the second weighted integral into a column integral of the same kernel.
private lemma integrated_bound (f : ℝ → ℝ) (hf : AEStronglyMeasurable f ray) :
    ∫⁻ s, ‖transform f s‖ₑ ^ 2 ∂ray ≤ gammaHalf ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ray := by
  let F x := ‖f x‖ₑ ^ 2 / weight x
  have hmeas : AEMeasurable (fun z : ℝ × ℝ => weight z.1 * (kernel z.1 z.2 * F z.2))
      (ray.prod ray) := by
    have := hf.comp_snd (μ := ray)
    dsimp [F, weight, kernel]
    fun_prop
  calc
    ∫⁻ s, ‖transform f s‖ₑ ^ 2 ∂ray
      ≤ ∫⁻ s, (gammaHalf * weight s) * ∫⁻ x, kernel s x * F x ∂ray ∂ray := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact norm_transform_sq_le f hf hs
    _ = gammaHalf * ∫⁻ s, ∫⁻ x, weight s * (kernel s x * F x) ∂ray ∂ray := by
        rw [← lintegral_const_mul' gammaHalf _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro s
        rw [lintegral_const_mul' (weight s) _ ENNReal.ofReal_ne_top, mul_assoc]
    _ = gammaHalf * ∫⁻ x, ∫⁻ s, weight s * (kernel s x * F x) ∂ray ∂ray := by
        rw [lintegral_lintegral_swap hmeas]
    _ = gammaHalf * ∫⁻ x, gammaHalf * ‖f x‖ₑ ^ 2 ∂ray := by
        congr 1
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
        have symmK (s : ℝ) : kernel s x = kernel x s := by simp [kernel, mul_comm]
        have hcol (s : ℝ) : weight s * (kernel s x * F x) = (kernel x s * weight s) * F x := by
          rw [symmK]
          ac_rfl
        simp_rw [hcol]
        rw [lintegral_mul_const (F x) (f := fun s => kernel x s * weight s)
          (by dsimp [kernel, weight]; fun_prop), weighted_row hx, mul_assoc,
          ENNReal.mul_div_cancel (weight_pos hx).ne' ENNReal.ofReal_ne_top]
    _ = _ := by rw [lintegral_const_mul' gammaHalf _ ENNReal.ofReal_ne_top, sq, mul_assoc]

private lemma bounded_two (f : ℝ → ℝ) (hf : MemLp f 2 ray) :
    MemLp (transform f) 2 ray ∧ eLpNorm (transform f) 2 ray ≤ gammaHalf * eLpNorm f 2 ray := by
  have hm : AEStronglyMeasurable (transform f) ray := by
    apply AEStronglyMeasurable.integral_prod_right' (f := fun z : ℝ × ℝ =>
      Real.exp (-z.2 * z.1) * f z.2)
    exact (by fun_prop : AEStronglyMeasurable (fun z : ℝ × ℝ => Real.exp (-z.2 * z.1)) _).mul
      hf.aestronglyMeasurable.comp_snd
  have norm_sq (g : ℝ → ℝ) (hg : AEStronglyMeasurable g ray) :
      eLpNorm g 2 ray ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ray := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hg
  have hle : eLpNorm (transform f) 2 ray ≤ gammaHalf * eLpNorm f 2 ray := by
    apply (ENNReal.rpow_le_rpow_iff (z := 2) (by norm_num)).mp
    rw [ENNReal.rpow_two, ENNReal.rpow_two, mul_pow, norm_sq _ hm,
      norm_sq _ hf.aestronglyMeasurable]
    exact integrated_bound f hf.aestronglyMeasurable
  exact ⟨hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top), hle⟩

private noncomputable abbrev intervalFn (t c : ℝ) := (Ioc 0 t).indicator (fun _ => c)

private lemma interval_measure (t : ℝ) : ray (Ioc 0 t) = ENNReal.ofReal t := by
  rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self,
    Real.volume_Ioc, sub_zero]

private lemma interval_norm {t : ℝ} (ht : 0 < t) (c : ℝ) {p : ℝ≥0∞} (hp : p ≠ 0) :
    eLpNorm (intervalFn t c) p ray = ‖c‖ₑ * ENNReal.ofReal t ^ (1 / p.toReal) := by
  rw [intervalFn, eLpNorm_indicator_const' measurableSet_Ioc.nullMeasurableSet
    (by rw [interval_measure]; exact (ENNReal.ofReal_pos.mpr ht).ne') hp, interval_measure]

-- On the rectangle (0,t] × (0,1/t] the kernel is at least exp(-1).
private lemma interval_lower {t : ℝ} (ht : 0 < t) (s : ℝ) :
    ‖intervalFn t⁻¹ (Real.exp (-1) * t) s‖ ≤ ‖transform (intervalFn t 1) s‖ := by
  by_cases hs : s ∈ Ioc 0 t⁻¹
  · rw [intervalFn, indicator_of_mem hs, Real.norm_of_nonneg (by positivity)]
    apply le_trans _ (le_abs_self _)
    have htI : IntegrableOn (fun x : ℝ => Real.exp (-x * s)) (Ioc 0 t) :=
      (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x * s))).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    calc
      Real.exp (-1) * t = ∫ _ : ℝ in Ioc 0 t, Real.exp (-1) := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le ht.le, sub_zero, smul_eq_mul, mul_comm]
      _ ≤ ∫ x : ℝ in Ioc 0 t, Real.exp (-x * s) := by
        refine setIntegral_mono_on ?_ htI measurableSet_Ioc ?_
        · exact integrableOn_const (by simp [Real.volume_Ioc])
        · intro x hx
          apply Real.exp_le_exp.mpr
          have := (mul_le_mul_of_nonneg_right hx.2 hs.1.le).trans
            (mul_le_mul_of_nonneg_left hs.2 ht.le)
          rwa [mul_inv_cancel₀ ht.ne', ← neg_le_neg_iff, ← neg_mul] at this
      _ = transform (intervalFn t 1) s := by
        simp only [transform, ray, intervalFn,
          ← indicator_mul_right (Ioc 0 t) (fun x => Real.exp (-x * s)) (fun _ => (1 : ℝ)), mul_one,
          setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self]
  · simp [intervalFn, indicator_of_notMem hs]

private lemma exponent_eq_two {p C : ℝ≥0∞} (hp : 1 ≤ p) (hC : C < ⊤)
    (h : ∀ f : ℝ → ℝ, MemLp f p ray → eLpNorm (transform f) p ray ≤ C * eLpNorm f p ray) :
    p = 2 := by
  -- The indicator norm formula also holds at infinity, where this reciprocal is zero.
  let q := 1 / p.toReal
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have bound (t : ℝ) (ht : 0 < t) : Real.exp (-1) * t * (t⁻¹) ^ q ≤ C.toReal * t ^ q := by
    have htest := h (intervalFn t 1) (memLp_indicator_const _ measurableSet_Ioc.nullMeasurableSet
      _ (Or.inr (by rw [interval_measure]; exact ENNReal.ofReal_ne_top)))
    have hle := (eLpNorm_mono (μ := ray) (p := p)
      (f := intervalFn t⁻¹ (Real.exp (-1) * t))
      (aestronglyMeasurable_const.indicator measurableSet_Ioc)
      (interval_lower ht)).trans htest
    rw [interval_norm (inv_pos.mpr ht) _ hp0, interval_norm ht _ hp0] at hle
    have hfin : C * (‖(1 : ℝ)‖ₑ * ENNReal.ofReal t ^ (1 / p.toReal)) ≠ ⊤ := by
      apply ENNReal.mul_ne_top hC.ne
      apply ENNReal.mul_ne_top (by simp)
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    have hreal := ENNReal.toReal_mono hfin hle
    simpa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal ht.le,
      ENNReal.toReal_ofReal (inv_pos.mpr ht).le, abs_of_pos ht, q] using hreal
  have power_bound (t : ℝ) (ht : 0 < t) : t ^ (1 - 2 * q) ≤ C.toReal / Real.exp (-1) := by
    have hb := bound t ht
    rw [Real.inv_rpow ht.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos ht _)] at hb
    rw [le_div_iff₀ (Real.exp_pos _), Real.rpow_sub ht, Real.rpow_one,
      two_mul, Real.rpow_add ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  by_contra hne
  have ha : 1 - 2 * q ≠ 0 := by
    intro ha
    have hq : q = 1 / 2 := by linarith
    have hr : p.toReal = 2 := by
      change 1 / p.toReal = 1 / 2 at hq
      simpa using congrArg Inv.inv hq
    have hpt : p ≠ ⊤ := by rintro rfl; simp at hr
    exact hne (by rw [← ENNReal.ofReal_toReal hpt, hr]; norm_num)
  let b := C.toReal / Real.exp (-1) + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hf := power_bound (b ^ (1 - 2 * q)⁻¹) (Real.rpow_pos_of_pos hb _)
  rw [← Real.rpow_mul hb.le, inv_mul_cancel₀ ha, Real.rpow_one] at hf
  dsimp [b] at hf
  linarith

/-- **The Laplace transform is bounded on $L^p([0,\infty))$ exactly when $p = 2$.** For a real
function $f$ on $\mathbb{R}$ let
$$Lf(s) = \int_0^\infty e^{-xs} f(x)\,dx \qquad (s \in \mathbb{R}).$$
Let $p \in [1,\infty]$. Then $p = 2$ if and only if there is a constant $C$ with $0 < C < \infty$
such that every real function $f \in L^p([0,\infty))$ satisfies $Lf \in L^p([0,\infty))$ and
$\|Lf\|_{L^p([0,\infty))} \le C\,\|f\|_{L^p([0,\infty))}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral,
integro-differential, and pseudodifferential operators),
`benchmark/level2/ma_proofbench_l2_31.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem laplaceTransform_bounded_on_Lp_iff_eq_two (p : ENNReal) (hp : 1 ≤ p) :
  (∃ C : ENNReal, 0 < C ∧ C < ⊤ ∧ ∀ f : ℝ → ℝ,
  MemLp f p (volume.restrict (Set.Ici (0 : ℝ))) →
  MemLp (fun s : ℝ => ∫ x in Set.Ici (0 : ℝ), Real.exp (-x * s) * f x) p
    (volume.restrict (Set.Ici (0 : ℝ))) ∧
  eLpNorm (fun s : ℝ => ∫ x in Set.Ici (0 : ℝ), Real.exp (-x * s) * f x) p
    (volume.restrict (Set.Ici (0 : ℝ))) ≤
  C * eLpNorm f p (volume.restrict (Set.Ici (0 : ℝ)))) ↔
  p = 2 := by
  simp only [← restrict_Ioi_eq_restrict_Ici]
  constructor
  · rintro ⟨C, _, hC, h⟩
    exact exponent_eq_two hp hC fun f hf => (h f hf).2
  · rintro rfl
    exact ⟨gammaHalf, ENNReal.ofReal_pos.mpr (Real.Gamma_pos_of_pos (by norm_num)),
      ENNReal.ofReal_lt_top, bounded_two⟩

end MathlibExt.Analysis.OperatorTheory.LaplaceTransformLpBoundedIffTwoWanted
