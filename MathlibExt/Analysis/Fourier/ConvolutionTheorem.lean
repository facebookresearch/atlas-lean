/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Fourier.FourierTransform

/-! # Convolution theorem for Fourier integrals on the real line

This file proves that the Fourier integral associated to a continuous additive character and a
sigma-finite translation-invariant measure turns convolution into pointwise multiplication.
-/

@[expose] public section

namespace MetaMathlibExt

open MeasureTheory
open scoped Convolution

private theorem convThm_isAddLeftInvariant {μ : Measure ℝ}
    (hinv : ∀ a : ℝ, MeasurePreserving (fun x => a + x) μ μ) :
    μ.IsAddLeftInvariant :=
  ⟨fun a => (hinv a).map_eq⟩

private theorem convThm_integrable_kernel {e : AddChar ℝ Circle} {μ : Measure ℝ}
    [SigmaFinite μ] [μ.IsAddRightInvariant] (he : Continuous e) {f g : ℝ → ℂ}
    (hf : Integrable f μ) (hg : Integrable g μ) (w : ℝ) :
    Integrable
      (fun p : ℝ × ℝ => e (-(p.1 * w)) • (f p.2 * g (p.1 - p.2)))
      (μ.prod μ) := by
  have hfg : Integrable
      (fun p : ℝ × ℝ =>
        (ContinuousLinearMap.lsmul ℂ ℂ (f p.2)) (g (p.1 - p.2)))
      (μ.prod μ) :=
    hf.convolution_integrand (ContinuousLinearMap.lsmul ℂ ℂ) hg
  have hmul : Integrable
      (fun p : ℝ × ℝ => f p.2 * g (p.1 - p.2)) (μ.prod μ) := by
    simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hfg
  refine hmul.mono ?_ ?_
  · exact (he.comp (by fun_prop)).aestronglyMeasurable.smul hmul.aestronglyMeasurable
  · filter_upwards with p
    simp [Circle.smul_def]

private theorem convThm_translate_inner {e : AddChar ℝ Circle} {μ : Measure ℝ}
    (hinv : ∀ a : ℝ, MeasurePreserving (fun x => a + x) μ μ)
    (f g : ℝ → ℂ) (w t : ℝ) :
    (∫ x, e (-(x * w)) • (f t * g (x - t)) ∂μ) =
      ∫ y, e (-((t + y) * w)) • (f t * g y) ∂μ := by
  simpa using
    ((hinv t).integral_comp (measurableEmbedding_addLeft t)
      (fun x : ℝ => e (-(x * w)) • (f t * g (x - t)))).symm

private theorem convThm_fourier_convolution_eq_double_integral
    {e : AddChar ℝ Circle} {μ : Measure ℝ} [SigmaFinite μ] [μ.IsAddRightInvariant]
    (he : Continuous e)
    (hinv : ∀ a : ℝ, MeasurePreserving (fun x => a + x) μ μ)
    {f g : ℝ → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (w : ℝ) :
    Fourier.fourierIntegral e μ
        (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, μ] g) w =
      ∫ t, ∫ y, e (-((t + y) * w)) • (f t * g y) ∂μ ∂μ := by
  calc
    _ = ∫ x, e (-(x * w)) • ∫ t, f t * g (x - t) ∂μ ∂μ := by
      simp only [Fourier.fourierIntegral_def, convolution_def,
        ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    _ = ∫ x, ∫ t, e (-(x * w)) • (f t * g (x - t)) ∂μ ∂μ := by
      congr
      ext x
      simp_rw [Circle.smul_def, integral_smul]
    _ = ∫ t, ∫ x, e (-(x * w)) • (f t * g (x - t)) ∂μ ∂μ :=
      integral_integral_swap (convThm_integrable_kernel he hf hg w)
    _ = ∫ t, ∫ y, e (-((t + y) * w)) • (f t * g y) ∂μ ∂μ := by
      congr with t
      exact convThm_translate_inner hinv f g w t

private theorem convThm_double_integral_eq_product {e : AddChar ℝ Circle}
    {μ : Measure ℝ} (f g : ℝ → ℂ) (w : ℝ) :
    (∫ t, ∫ y, e (-((t + y) * w)) • (f t * g y) ∂μ ∂μ) =
      Fourier.fourierIntegral e μ f w * Fourier.fourierIntegral e μ g w := by
  calc
    _ = ∫ t, ∫ y,
        (e (-(t * w)) • f t) * (e (-(y * w)) • g y) ∂μ ∂μ := by
      congr with t
      congr with y
      rw [add_mul, neg_add, AddChar.map_add_eq_mul, mul_smul]
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    _ = ∫ t, (e (-(t * w)) • f t) *
        (∫ y, e (-(y * w)) • g y ∂μ) ∂μ := by
      congr with t
      rw [integral_const_mul]
    _ = (∫ t, e (-(t * w)) • f t ∂μ) *
        (∫ y, e (-(y * w)) • g y ∂μ) := by
      rw [integral_mul_const]
    _ = Fourier.fourierIntegral e μ f w * Fourier.fourierIntegral e μ g w := by
      rw [Fourier.fourierIntegral_def, Fourier.fourierIntegral_def]

/-- Convolution theorem: the Fourier transform turns convolution into pointwise
product. For a sigma-finite translation-invariant Borel measure `μ` and integrable
`f g : ℝ → ℂ`, the Fourier transform of the Mathlib convolution
`(f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, μ] g)` at `w` equals the pointwise product
of the Fourier transforms at `w`.
Source: https://en.wikipedia.org/wiki/Convolution_theorem
(statement `convolution-theorem-s1`).

Proves `Wanted` entry `convolution_theorem`.

Proof: The proof uses convolution-integrand integrability, Fubini, translation invariance, and
character factorization, following Stein--Shakarchi, Ch. 5, Prop. 1.11, and Mathlib's
`Real.fourier_bilin_convolution_eq_integral`.
-/
theorem convolution_theorem {e : AddChar ℝ Circle}
    {μ : MeasureTheory.Measure ℝ} [MeasureTheory.SigmaFinite μ] (he : Continuous e)
    (hinv : ∀ a : ℝ, MeasureTheory.MeasurePreserving (fun x => a + x) μ μ)
    {f g : ℝ → ℂ}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ)
    (w : ℝ) :
    Fourier.fourierIntegral e μ
      (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, μ] g) w =
      Fourier.fourierIntegral e μ f w * Fourier.fourierIntegral e μ g w := by
  let _ : μ.IsAddLeftInvariant := convThm_isAddLeftInvariant hinv
  let _ : μ.IsAddRightInvariant := IsAddLeftInvariant.isAddRightInvariant
  calc
    _ = ∫ t, ∫ y, e (-((t + y) * w)) • (f t * g y) ∂μ ∂μ :=
      convThm_fourier_convolution_eq_double_integral he hinv hf hg w
    _ = _ := convThm_double_integral_eq_product f g w

end MetaMathlibExt

end
