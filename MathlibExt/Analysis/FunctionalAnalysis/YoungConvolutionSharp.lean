/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:
`benchmark/level1/ma_proofbench_l1_45.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029).
Copyright holder: OpenBMB. License: MIT. Authors: L. Pu et al. (MA-ProofBench).
The adaptation is limited to the statement of `exists_eLpNorm_convolution_gt_one_sub_mul`.

Copyright (c) 2026 OpenBMB

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

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Sharpness of Young's convolution inequality on the real line

The theorem `exists_eLpNorm_convolution_gt_one_sub_mul` proves sharpness of the constant
in Young's $L^1$–$L^p$ convolution inequality using indicators of intervals.
-/

open MeasureTheory Set Convolution

namespace MathlibExt.Analysis.FunctionalAnalysis.YoungConvolutionSharpWanted

private noncomputable def intervalIndicator (a b c : ℝ) : ℝ → ℝ :=
  (Icc a b).indicator (fun _ ↦ c)

private theorem memLp_intervalIndicator (a b c : ℝ) (p : ENNReal) :
    MemLp (intervalIndicator a b c) p :=
  memLp_indicator_const p measurableSet_Icc.nullMeasurableSet c
    (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))

private theorem toReal_eLpNorm_intervalIndicator {a b : ℝ} (c : ℝ) {p : ENNReal}
    (hab : a < b) (hp : p ≠ 0) :
    (eLpNorm (intervalIndicator a b c) p).toReal = ‖c‖ * (b - a) ^ (1 / p.toReal) := by
  have hvol : volume (Icc a b) ≠ 0 := by
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  rw [intervalIndicator, eLpNorm_indicator_const' measurableSet_Icc.nullMeasurableSet hvol hp,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  simp

private theorem convolution_intervalIndicator (δ x : ℝ) :
    (intervalIndicator 0 δ 1 ⋆ intervalIndicator 0 1 1) x =
      max (min δ x - max 0 (x - 1)) 0 := by
  -- The integrand is the indicator of the intersection of the two intervals.
  have hintegrand : (fun t ↦ intervalIndicator 0 δ 1 t * intervalIndicator 0 1 1 (x - t)) =
      intervalIndicator (max 0 (x - 1)) (min δ x) 1 := by
    funext t
    have hmem : t ∈ Icc (max 0 (x - 1)) (min δ x) ↔
        t ∈ Icc 0 δ ∧ x - t ∈ Icc 0 1 := by
      simp only [mem_Icc, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨ht, hxt⟩, htδ, htx⟩
        exact ⟨⟨ht, htδ⟩, by linarith, by linarith⟩
      · rintro ⟨⟨ht, htδ⟩, hxt, htx⟩
        exact ⟨⟨ht, by linarith⟩, htδ, by linarith⟩
    by_cases ht : t ∈ Icc 0 δ <;> by_cases hx : x - t ∈ Icc (0 : ℝ) 1 <;>
      simp [intervalIndicator, hmem, ht, hx]
  change (∫ t, intervalIndicator 0 δ 1 t * intervalIndicator 0 1 1 (x - t)) = _
  rw [hintegrand, intervalIndicator, integral_indicator_const _ measurableSet_Icc]
  simp [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal']

private theorem memLp_convolution_intervalIndicator {δ : ℝ} (hδ : 0 ≤ δ) (p : ENNReal) :
    MemLp (intervalIndicator 0 δ 1 ⋆ intervalIndicator 0 1 1) p := by
  -- An interval containing the support gives finiteness of the convolution norm.
  apply (memLp_intervalIndicator 0 (1 + δ) δ p).mono'
  · exact (memLp_intervalIndicator 0 δ 1 1).aestronglyMeasurable.convolution _
      (memLp_intervalIndicator 0 1 1 p).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [convolution_intervalIndicator, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _),
      intervalIndicator]
    by_cases hx : x ∈ Icc 0 (1 + δ)
    · rw [indicator_of_mem hx]
      exact max_le (by linarith only [min_le_left δ x, le_max_left 0 (x - 1)]) hδ
    · rw [indicator_of_notMem hx]
      have hx' : x < 0 ∨ 1 + δ < x := by simpa only [mem_Icc, not_and_or, not_le] using hx
      refine max_le ?_ le_rfl
      rcases hx' with hx' | hx'
      · linarith only [hx', min_le_right δ x, le_max_left 0 (x - 1)]
      · linarith only [hx', min_le_left δ x, le_max_right 0 (x - 1)]

private theorem toReal_eLpNorm_intervalIndicator_le_convolution {δ : ℝ}
    (hδ : 0 ≤ δ) (p : ENNReal) :
    (eLpNorm (intervalIndicator δ 1 δ) p).toReal ≤
      (eLpNorm (intervalIndicator 0 δ 1 ⋆ intervalIndicator 0 1 1) p).toReal := by
  apply ENNReal.toReal_mono (memLp_convolution_intervalIndicator hδ p).eLpNorm_ne_top
  apply eLpNorm_mono (memLp_intervalIndicator δ 1 δ p).aestronglyMeasurable
  intro x
  -- On this interval, every point of the support of the first factor contributes.
  rw [intervalIndicator]
  by_cases hx : x ∈ Icc δ 1
  · rw [indicator_of_mem hx, convolution_intervalIndicator, min_eq_left hx.1,
      max_eq_left (sub_nonpos.mpr hx.2), sub_zero, max_eq_left hδ]
  · rw [indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _

/-- **The constant in Young's $L^1$–$L^p$ convolution inequality cannot be lowered.** Let
$1 \le p \le \infty$ and $\varepsilon > 0$. Then there exist real-valued functions
$f \in L^1(\mathbb{R})$ and $g \in L^p(\mathbb{R})$ such that
$$
\|f * g\|_p > (1 - \varepsilon) \|f\|_1 \|g\|_p,
$$
where $(f * g)(x) = \int_{\mathbb{R}} f(t)\, g(x - t)\, dt$ and all norms are taken with
respect to Lebesgue measure.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_45.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_eLpNorm_convolution_gt_one_sub_mul
    (p : ENNReal) (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f g : ℝ → ℝ), MemLp f 1 ∧ MemLp g p ∧
      (eLpNorm (f ⋆ g) p).toReal > ((1 - ε) * (eLpNorm f 1).toReal * (eLpNorm g p).toReal) := by
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_one : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  let f := intervalIndicator 0 δ 1
  let g := intervalIndicator 0 1 1
  have hf : MemLp f 1 := memLp_intervalIndicator 0 δ 1 1
  have hg : MemLp g p := memLp_intervalIndicator 0 1 1 p
  refine ⟨f, g, hf, hg, ?_⟩
  have hnorm := toReal_eLpNorm_intervalIndicator_le_convolution hδ.le p
  have hp_zero : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hexp : 1 / p.toReal ≤ 1 := by
    simpa only [one_div, ENNReal.toReal_inv, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (ENNReal.inv_le_one.mpr hp)
  have hpow : 1 - δ ≤ (1 - δ) ^ (1 / p.toReal) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr hδ_one) (sub_le_self _ hδ.le) hexp
  rw [toReal_eLpNorm_intervalIndicator δ hδ_one hp_zero, Real.norm_eq_abs,
    abs_of_nonneg hδ.le] at hnorm
  have hf_norm : (eLpNorm f 1).toReal = δ := by
    simpa only [norm_one, sub_zero, ENNReal.toReal_one, div_one, Real.rpow_one, one_mul] using
      toReal_eLpNorm_intervalIndicator 1 hδ one_ne_zero
  have hg_norm : (eLpNorm g p).toReal = 1 := by
    simpa only [norm_one, sub_zero, Real.one_rpow, one_mul] using
      toReal_eLpNorm_intervalIndicator 1 zero_lt_one hp_zero
  have hstrict : (1 - ε) * δ < δ * (1 - δ) := by
    rw [mul_comm δ (1 - δ)]
    exact mul_lt_mul_of_pos_right (sub_lt_sub_left hδε 1) hδ
  rw [hf_norm, hg_norm, mul_one]
  exact hstrict.trans_le ((mul_le_mul_of_nonneg_left hpow hδ.le).trans hnorm)

end MathlibExt.Analysis.FunctionalAnalysis.YoungConvolutionSharpWanted
