/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_05.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), for the seminorm definition, theorem statement,
and problem description.
Copyright (c) 2026 OpenBMB. Licensed under the MIT License, reproduced below.
Authors: L. Pu et al. (MA-ProofBench)

The ATLAS version names and documents the declarations, places them in a namespace, and
supplies a proof.

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

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Sup-norm bound for high-frequency Schwartz functions

Fourier inversion and Cauchy–Schwarz bound the supremum norm by the homogeneous Sobolev
seminorm times `√(2 / (2s - 1)) * A ^ (1/2 - s)` when the Fourier support avoids `[-A, A]`.
-/

@[expose] public section

open MeasureTheory Set
open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.HighFrequencySupNormSobolevBoundWanted

/-- **Homogeneous Sobolev seminorm for the high-frequency sup-norm bound.** For a real number $s$
and a Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with Fourier transform
$\hat f(\xi) = \int_{\mathbb{R}} e^{-2\pi i x \xi} f(x) \, dx$, the homogeneous Sobolev seminorm
of $f$ is
$$
\|f\|_{\dot H^s} = \left( \int_{\mathbb{R}} |\xi|^{2s} \, |\hat f(\xi)|^2 \, d\xi \right)^{1/2},
$$
where the integral is taken to be $0$ when the integrand is not integrable. -/
noncomputable def dotHSeminorm (s : ℝ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  Real.sqrt (∫ ξ : ℝ, Real.rpow ‖ξ‖ (2 * s) * ‖(𝓕 f) ξ‖ ^ 2)

private lemma memLp_weighted_norm {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (g : SchwartzMap ℝ ℂ) : MemLp (fun ξ ↦ ‖ξ‖ ^ s * ‖g ξ‖) 2 := by
  let xg := SchwartzMap.smulLeftCLM ℂ (id : ℝ → ℝ) g
  refine ((g.memLp 2).norm.add (xg.memLp 2).norm).mono'
    (f := fun ξ ↦ ‖ξ‖ ^ s * ‖g ξ‖) (by fun_prop) ?_
  refine ae_of_all _ fun ξ ↦ ?_
  have h : ‖ξ‖ ^ s ≤ 1 + ‖ξ‖ := calc
    _ ≤ (1 + ‖ξ‖) ^ s := Real.rpow_le_rpow (norm_nonneg _) (by linarith) hs₀
    _ ≤ _ := Real.rpow_le_self_of_one_le (by linarith [norm_nonneg ξ]) hs₁
  change ‖‖ξ‖ ^ s * ‖g ξ‖‖ ≤ ‖g ξ‖ + ‖xg ξ‖
  rw [Real.norm_of_nonneg (by positivity), show xg ξ = ξ • g ξ from
    SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) g ξ, norm_smul, ← one_add_mul]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

private lemma integral_tail_weight_sq {A s : ℝ} (hA : 0 < A) (hs : 1 / 2 < s) :
    (∫ ξ : ℝ, ((Ioi A).indicator (fun r ↦ r ^ (-s)) |ξ|) ^ 2) =
      2 / (2 * s - 1) * A ^ (-2 * s + 1) := by
  calc
    _ = ∫ ξ : ℝ, (Ioi A).indicator (fun r ↦ r ^ (-2 * s)) |ξ| := by
      apply integral_congr_ae
      refine ae_of_all _ fun ξ ↦ ?_
      by_cases hξ : |ξ| ∈ Ioi A
      · simp only [indicator_of_mem hξ, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg ξ)]
        ring_nf
      · simp [indicator_of_notMem hξ]
    _ = _ := by
      rw [integral_comp_abs, setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi hA.le), integral_Ioi_rpow_of_lt (by linarith) hA]
      rw [show -2 * s + 1 = -(2 * s - 1) by ring, div_neg, neg_div, neg_neg]
      ring

/-- **Sup bound for Schwartz functions with high-frequency Fourier support.** Let
$s \in (\tfrac12, 1]$, and for a Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with Fourier
transform $\hat f$ let
$\|f\|_{\dot H^s} = \left( \int_{\mathbb{R}} |\xi|^{2s} |\hat f(\xi)|^2 \, d\xi \right)^{1/2}$
be its homogeneous Sobolev seminorm. There is a constant $C_2 > 0$ such that for every real
$A > 0$ and every Schwartz function $f : \mathbb{R} \to \mathbb{C}$ whose Fourier transform has
closed support contained in $\mathbb{R} \setminus [-A, A]$,
$$
\sup_{x \in \mathbb{R}} |f(x)| \le C_2 \, A^{-s + \frac12} \, \|f\|_{\dot H^s}.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_05.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem sSup_norm_le_rpow_mul_dotHSeminorm_of_tsupport_fourier_compl_Icc
    (s : ℝ) (hs : s ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    ∃ C2 > 0, ∀ (A : NNReal),
      0 < (A : ℝ) →
      ∀ f : SchwartzMap ℝ ℂ,
        tsupport (fun ξ : ℝ => (𝓕 f) ξ) ⊆ (Set.Icc (-(A : ℝ)) (A : ℝ))ᶜ →
          sSup (Set.range (fun x : ℝ => ‖f x‖)) ≤
            C2 * Real.rpow (A : ℝ) (-s + 1 / 2) * dotHSeminorm s f := by
  have hs' := hs.1
  have hden : 0 < 2 * s - 1 := by linarith
  refine ⟨Real.sqrt (2 / (2 * s - 1)), by positivity, ?_⟩
  intro A hA f hf
  let w := fun ξ : ℝ ↦ (Ioi (A : ℝ)).indicator (fun r ↦ r ^ (-s)) |ξ|
  let v := fun ξ : ℝ ↦ ‖ξ‖ ^ s * ‖(𝓕 f) ξ‖
  have hw_sq : (∫ ξ, w ξ ^ 2) = 2 / (2 * s - 1) * (A : ℝ) ^ (-2 * s + 1) :=
    integral_tail_weight_sq hA hs'
  have hw : MemLp w 2 := by
    have hm : Measurable (fun r : ℝ ↦ r ^ (-s)) := by fun_prop
    have hwm : Measurable w := (hm.indicator measurableSet_Ioi).comp (by fun_prop)
    apply (memLp_two_iff_integrable_sq hwm.aestronglyMeasurable).2
    apply Integrable.of_integral_ne_zero
    rw [hw_sq]
    positivity
  have hv : MemLp v 2 := memLp_weighted_norm (by linarith) hs.2 (𝓕 f)
  have hwv (ξ : ℝ) : w ξ * v ξ = ‖(𝓕 f) ξ‖ := by
    by_cases hξ : (A : ℝ) < |ξ|
    · dsimp only [v]
      rw [show w ξ = |ξ| ^ (-s) from indicator_of_mem hξ _,
        Real.norm_eq_abs, ← mul_assoc, ← Real.rpow_add (hA.trans hξ)]
      simp
    · have hzero : (𝓕 f) ξ = 0 := image_eq_zero_of_notMem_tsupport
          (fun hx ↦ hf hx (abs_le.mp (le_of_not_gt hξ)))
      simp [v, hzero]
  have hv_sq (ξ : ℝ) : v ξ ^ 2 = ‖ξ‖ ^ (2 * s) * ‖(𝓕 f) ξ‖ ^ 2 := by
    dsimp only [v]
    rw [mul_pow, ← Real.rpow_two (‖ξ‖ ^ s),
      ← Real.rpow_mul (norm_nonneg ξ), mul_comm s]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := w) (g := v)
    (ae_of_all _ fun ξ ↦ indicator_nonneg (fun r hr ↦ Real.rpow_nonneg (hA.trans hr).le _) _)
    (ae_of_all _ fun ξ ↦ show 0 ≤ ‖ξ‖ ^ s * ‖(𝓕 f) ξ‖ by positivity)
    (by simpa using hw) (by simpa using hv)
  simp only [hwv, Real.rpow_two, hv_sq, ← Real.sqrt_eq_rpow] at hCS
  rw [hw_sq, Real.sqrt_mul (by positivity),
    Real.sqrt_eq_rpow (↑A ^ _), ← Real.rpow_mul hA.le,
    show (-2 * s + 1) * (1 / 2) = -s + 1 / 2 by ring] at hCS
  apply csSup_le (range_nonempty _)
  rintro _ ⟨x, rfl⟩
  calc
    ‖f x‖ = ‖(𝓕⁻ (𝓕 f)) x‖ := by rw [FourierTransform.fourierInv_fourier_eq]
    _ ≤ ∫ ξ, ‖(𝓕 f) ξ‖ := Real.norm_fourier_le_integral_norm (𝓕 f : SchwartzMap ℝ ℂ) (-x)
    _ ≤ _ := hCS

end MathlibExt.Analysis.Fourier.HighFrequencySupNormSobolevBoundWanted
