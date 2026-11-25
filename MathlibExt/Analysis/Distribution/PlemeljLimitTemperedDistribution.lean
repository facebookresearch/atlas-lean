/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_15.lean` (openbmb/ma-proofbench, commit 31bab4c7):
the two pairing definitions and the statement of the convergence theorem.
Authors: L. Pu et al. (MA-ProofBench). Licensed under the MIT License below.

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

-- Preserve the complex normed-ring instance in the original distribution space.
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Distributional limits of the Cauchy kernels

The kernels `(x ± ε I)⁻¹` define tempered distributions for positive `ε` and converge
on Schwartz functions as `ε` tends to zero from the right. Their Fourier representations
allow dominated convergence against an integrable Schwartz function.
-/

open Filter MeasureTheory Set
open scoped FourierTransform Real Topology

namespace MathlibExt.Analysis.Distribution.PlemeljLimitTemperedDistributionWanted

noncomputable section

/-- **The pairing with $(x + i\varepsilon)^{-1}$.** For a real number $\varepsilon$ and a Schwartz
function $\phi : \mathbb{R} \to \mathbb{C}$, $u_{+,\varepsilon}(\phi)$ is the complex number
$\int_{\mathbb{R}} (x + i\varepsilon)^{-1}\phi(x)\, dx$.

The integral is the Lebesgue integral, taken to be $0$ when the integrand is not integrable;
this can happen only for $\varepsilon = 0$.
-/
@[expose] public def uPlusEps (ε : ℝ) (φ : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ, (((x : ℂ) + (ε : ℂ) * Complex.I)⁻¹) * φ x

/-- **The pairing with $(x - i\varepsilon)^{-1}$.** For a real number $\varepsilon$ and a Schwartz
function $\phi : \mathbb{R} \to \mathbb{C}$, $u_{-,\varepsilon}(\phi)$ is the complex number
$\int_{\mathbb{R}} (x - i\varepsilon)^{-1}\phi(x)\, dx$.

The integral is the Lebesgue integral, taken to be $0$ when the integrand is not integrable;
this can happen only for $\varepsilon = 0$.
-/
@[expose] public def uMinusEps (ε : ℝ) (φ : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ, (((x : ℂ) - (ε : ℂ) * Complex.I)⁻¹) * φ x

/-- The exponential damping on the positive half-line, including its undamped value at zero. -/
private def damping (ε : ℝ) : ℝ → ℂ :=
  (Ioi 0).indicator fun t : ℝ => Complex.exp ((-2 * π * ε : ℝ) * (t : ℂ))

private lemma damping_measurable (ε : ℝ) : Measurable (damping ε) :=
  Measurable.indicator (by fun_prop) measurableSet_Ioi

private lemma norm_damping_le_one {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : ‖damping ε t‖ ≤ 1 := by
  by_cases ht : 0 < t
  · simp only [damping, indicator_of_mem (mem_Ioi.mpr ht), Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hε) ht.le
  · simp [damping, ht]

private lemma damping_memLp {ε : ℝ} (hε : 0 ≤ ε) : MemLp (damping ε) ⊤ volume :=
  memLp_top_of_bound (damping_measurable ε).aestronglyMeasurable 1
    (ae_of_all _ (norm_damping_le_one hε))

private def halfLine {ε : ℝ} (hε : 0 ≤ ε) : TemperedDistribution ℝ ℂ :=
  Lp.toTemperedDistribution ((damping_memLp hε).toLp _)

private lemma halfLine_apply {ε : ℝ} (hε : 0 ≤ ε) (φ : SchwartzMap ℝ ℂ) :
    halfLine hε φ = ∫ t, damping ε t * φ t := by
  rw [halfLine, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(damping_memLp hε).coeFn_toLp] with t ht
  simp [ht, mul_comm]

private lemma tendsto_damping_integral (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun ε => ∫ t, damping ε t * φ t) (𝓝[>] 0) (𝓝 (halfLine (le_refl 0) φ)) := by
  rw [halfLine_apply]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖φ t‖)
  · exact .of_forall fun ε =>
      ((damping_measurable ε).mul φ.continuous.measurable).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ae_of_all _ fun t => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_damping_le_one (le_of_lt hε) t)
  · exact φ.integrable.norm
  · apply ae_of_all
    intro t
    by_cases ht : 0 < t
    · simp only [damping, indicator_of_mem (mem_Ioi.mpr ht)]
      apply ContinuousWithinAt.tendsto
      fun_prop
    · simp [damping, ht]

private lemma damping_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (damping ε) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioi
  apply integrableOn_exp_mul_complex_Ioi
  simp only [Complex.ofReal_re]
  exact mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) hε

private def fourierFactor : ℂ := 2 * π * Complex.I

private lemma fourier_damping {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    fourierFactor * 𝓕 (damping ε) x = ((x : ℂ) - ε * Complex.I)⁻¹ := by
  let a : ℂ := (-2 * π * ε : ℝ) - 2 * π * x * Complex.I
  have ha : a.re < 0 := by
    simpa [a, Complex.mul_re] using (show 0 < 2 * π * ε by positivity)
  have htransform : 𝓕 (damping ε) x = ∫ t : ℝ in Ioi 0, Complex.exp (a * t) := by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_indicator measurableSet_Ioi]
    congr 1
    ext t
    by_cases ht : 0 < t
    · simp only [damping, indicator_of_mem (mem_Ioi.mpr ht), smul_eq_mul, ← Complex.exp_add]
      congr 1
      push_cast [a]
      ring
    · simp [damping, ht]
  have hfactor : a = -(fourierFactor * ((x : ℂ) - ε * Complex.I)) := by
    dsimp [a, fourierFactor]
    push_cast
    linear_combination (-2 * (π : ℂ) * ε) * Complex.I_sq
  rw [htransform, integral_exp_mul_complex_Ioi ha, hfactor]
  have hc : fourierFactor ≠ 0 := by simp [fourierFactor, Real.pi_ne_zero]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, one_div]
  rw [mul_inv_rev, mul_left_comm, mul_inv_cancel₀ hc, mul_one]

private lemma fourierInv_damping {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    -fourierFactor * 𝓕⁻ (damping ε) x = ((x : ℂ) + ε * Complex.I)⁻¹ := by
  rw [Real.fourierInv_eq_fourier_neg, neg_mul, fourier_damping hε, Complex.ofReal_neg,
    ← neg_add', inv_neg, neg_neg]

private lemma minus_pairing {ε : ℝ} (hε : 0 < ε) (φ : SchwartzMap ℝ ℂ) :
    fourierFactor * (∫ t, damping ε t * 𝓕 φ t) = uMinusEps ε φ := by
  have hswap : (∫ x, 𝓕 (damping ε) x * φ x) = ∫ t, damping ε t * 𝓕 φ t := by
    simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (.mul ℂ ℂ) (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
      (damping_integrable hε) φ.integrable
  rw [← hswap, ← integral_const_mul]
  simp only [← mul_assoc, fourier_damping hε, uMinusEps]

private lemma plus_pairing {ε : ℝ} (hε : 0 < ε) (φ : SchwartzMap ℝ ℂ) :
    -fourierFactor * (∫ t, damping ε t * 𝓕⁻ φ t) = uPlusEps ε φ := by
  have hflip : (-(innerₗ ℝ)).flip = -(innerₗ ℝ) := by
    ext
    simp
  have hswap : (∫ x, 𝓕⁻ (damping ε) x * φ x) = ∫ t, damping ε t * 𝓕⁻ φ t := by
    simp only [SchwartzMap.fourierInv_coe]
    simpa [hflip] using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (.mul ℂ ℂ) (L := -(innerₗ ℝ)) Real.continuous_fourierChar continuous_inner.neg
      (damping_integrable hε) φ.integrable
  rw [← hswap, ← integral_const_mul]
  simp only [← mul_assoc, fourierInv_damping hε, uPlusEps]

/-- **The tempered distributions $(x \pm i\varepsilon)^{-1}$ converge as $\varepsilon \to 0^+$.**
Write $S(\mathbb{R})$ for the space of complex-valued Schwartz functions on $\mathbb{R}$, and for
$\varepsilon > 0$ and $\phi \in S(\mathbb{R})$ let
$u_{\pm,\varepsilon}(\phi) = \int_{\mathbb{R}} (x \pm i\varepsilon)^{-1}\phi(x)\, dx$. Then for
every $\varepsilon > 0$ both $u_{+,\varepsilon}$ and $u_{-,\varepsilon}$ are tempered
distributions, that is, continuous $\mathbb{C}$-linear functionals on $S(\mathbb{R})$, and there
are tempered distributions $u_+$ and $u_-$ such that $u_{+,\varepsilon}(\phi) \to u_+(\phi)$ and
$u_{-,\varepsilon}(\phi) \to u_-(\phi)$ as $\varepsilon \to 0^+$ for every $\phi \in S(\mathbb{R})$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_15.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_temperedDistribution_tendsto_inv_add_mul_I :
    (∀ ε > 0,
      ∃ uPlus_eps uMinus_eps : TemperedDistribution ℝ ℂ,
        (∀ φ : SchwartzMap ℝ ℂ, uPlus_eps φ = uPlusEps ε φ) ∧
          (∀ φ : SchwartzMap ℝ ℂ, uMinus_eps φ = uMinusEps ε φ)) ∧
    (∃ uPlus uMinus : TemperedDistribution ℝ ℂ,
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun ε : ℝ => uPlusEps ε φ)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (uPlus φ))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun ε : ℝ => uMinusEps ε φ)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (uMinus φ)))) := by
  constructor
  · intro ε hε
    refine ⟨-fourierFactor • 𝓕⁻ (halfLine hε.le), fourierFactor • 𝓕 (halfLine hε.le), ?_, ?_⟩
    · intro φ
      change -fourierFactor * halfLine hε.le (𝓕⁻ φ) = _
      rw [halfLine_apply, plus_pairing hε]
    · intro φ
      change fourierFactor * halfLine hε.le (𝓕 φ) = _
      rw [halfLine_apply, minus_pairing hε]
  · refine ⟨-fourierFactor • 𝓕⁻ (halfLine (le_refl 0)), fourierFactor • 𝓕 (halfLine (le_refl 0)),
      ?_, ?_⟩
    · intro φ
      apply ((tendsto_damping_integral (𝓕⁻ φ)).const_mul (-fourierFactor)).congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε using plus_pairing hε φ
    · intro φ
      apply ((tendsto_damping_integral (𝓕 φ)).const_mul fourierFactor).congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε using minus_pairing hε φ

end

end MathlibExt.Analysis.Distribution.PlemeljLimitTemperedDistributionWanted
