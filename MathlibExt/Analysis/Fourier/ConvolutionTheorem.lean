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

/-- **Convolution theorem.** Let $e$ be a continuous additive character from $\mathbb{R}$ to the
unit circle, and let $\mu$ be a σ-finite measure on $\mathbb{R}$ that is preserved by every
translation $x \mapsto a + x$. For $\varphi : \mathbb{R} \to \mathbb{C}$ write
$\hat\varphi(w) = \int e(-xw)\,\varphi(x)\,d\mu(x)$ for its Fourier transform with respect to
$e$ and $\mu$, and for $f, g : \mathbb{R} \to \mathbb{C}$ write
$(f * g)(x) = \int f(t)\,g(x - t)\,d\mu(t)$ for their convolution. If $f$ and $g$ are
$\mu$-integrable, then $\widehat{f * g}(w) = \hat f(w)\,\hat g(w)$ for every $w \in \mathbb{R}$.

Proves `Wanted` entry `convolution_theorem`.

Proof: Integrability of the convolution integrand, Fubini's theorem, translation invariance of
$\mu$ and multiplicativity of $e$, following Stein--Shakarchi, Ch. 5, Prop. 1.11.

Source: https://en.wikipedia.org/wiki/Convolution_theorem
(statement `convolution-theorem-s1`).
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
