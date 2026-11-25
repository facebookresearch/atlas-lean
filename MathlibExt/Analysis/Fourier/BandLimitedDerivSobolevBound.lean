/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_00.lean` (openbmb/ma-proofbench, commit 31bab4c7):
the homogeneous Sobolev seminorm definition and the Bernstein inequality statement.
Authors: L. Pu et al. (MA-ProofBench). Licensed under the MIT License.

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

-- Supply the complex normed ring instance used by `deriv` in the source statement.
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# A Bernstein inequality for band-limited Schwartz functions

The homogeneous Sobolev seminorm bounds the supremum of the derivative of a Schwartz
function whose Fourier transform is supported in a bounded interval.
-/

@[expose] public section

open MeasureTheory Set
open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.BandLimitedDerivSobolevBoundWanted

/-- **Homogeneous Sobolev seminorm (band-limited derivative bound).** For
$s \in \mathbb{R}$ and a Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with Fourier transform
$\hat f(\xi) = \int_{\mathbb{R}} f(x) e^{-2\pi i x\xi}\,dx$, the homogeneous Sobolev seminorm of
order $s$ is
$$\|f\|_{\dot H^s} = \left(\int_{\mathbb{R}} |\xi|^{2s}\, |\hat f(\xi)|^2\,d\xi\right)^{1/2},$$
where the integral is taken to be $0$ when its integrand is not integrable. -/
noncomputable def dotHSeminorm (s : ℝ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  Real.sqrt (∫ ξ : ℝ, Real.rpow ‖ξ‖ (2 * s) * ‖(𝓕 f) ξ‖ ^ 2)

private theorem norm_deriv_le_fourier_moment (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖deriv f x‖ ≤ 2 * Real.pi * ∫ ξ : ℝ, ‖ξ‖ * ‖(𝓕 f) ξ‖ := by
  let d := SchwartzMap.derivCLM ℝ ℂ f
  have hinv := d.continuous.fourierInv_fourier_eq d.integrable (𝓕 d).integrable
  calc
    ‖deriv f x‖ = ‖𝓕 (𝓕 (deriv f)) (-x)‖ := by
      rw [← Real.fourierInv_eq_fourier_neg]
      exact congrArg (fun g : ℝ → ℂ ↦ ‖g x‖) hinv.symm
    _ ≤ ∫ ξ : ℝ, ‖𝓕 (deriv f) ξ‖ := Real.norm_fourier_le_integral_norm _ _
    _ = _ := by
      rw [Real.fourier_deriv f.integrable f.differentiable d.integrable, ← integral_const_mul]
      congr 1
      funext ξ
      simp [mul_assoc, SchwartzMap.fourier_coe]

-- Cauchy–Schwarz against the constant one gives the square root of the bandwidth.
private theorem integral_le_sqrt_length_mul (A : NNReal) (g : ℝ → ℝ) (hg : Continuous g)
    (hg₀ : ∀ ξ, 0 ≤ g ξ) :
    ∫ ξ in Icc (-A : ℝ) A, g ξ ≤
      Real.sqrt (2 * A) * Real.sqrt (∫ ξ in Icc (-A : ℝ) A, g ξ ^ 2) := by
  let μ := volume.restrict (Icc (-A : ℝ) A)
  have hg₂ : MemLp g 2 μ := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
    (hg.pow 2).integrableOn_Icc
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun _ ↦ (1 : ℝ)) (g := g) (.of_forall fun _ ↦ zero_le_one)
    (.of_forall hg₀) (memLp_const 1) (by simpa using hg₂)
  have hlen : volume.real (Icc (-A : ℝ) A) = 2 * A := by
    rw [Real.volume_real_Icc_of_le (by linarith [A.coe_nonneg])]
    ring
  simpa only [μ, one_mul, one_pow, Real.rpow_two, setIntegral_const, smul_eq_mul,
    mul_one, hlen, ← Real.sqrt_eq_rpow] using h

/-- **Bernstein-type bound for the derivative of a band-limited Schwartz function.** Let
$s \in (\tfrac12, 1]$. For a Schwartz function $f : \mathbb{R} \to \mathbb{C}$ write
$\hat f(\xi) = \int_{\mathbb{R}} f(x) e^{-2\pi i x\xi}\,dx$ for its Fourier transform and
$\|f\|_{\dot H^s} = \left(\int_{\mathbb{R}} |\xi|^{2s} |\hat f(\xi)|^2\,d\xi\right)^{1/2}$ for
its homogeneous Sobolev seminorm. There is a constant $C_1 > 0$ such that for every real
$A \ge 0$ and every Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with $\hat f(\xi) = 0$
whenever $|\xi| > A$,
$$\sup_{x \in \mathbb{R}} |f'(x)| \le C_1 A^{3/2 - s}\, \|f\|_{\dot H^s}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_00.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem norm_deriv_le_rpow_mul_dotHSeminorm_of_fourier_support_Icc
    (s : ℝ) (hs : s ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    ∃ C1 > 0, ∀ (A : NNReal),
      ∀ f : SchwartzMap ℝ ℂ,
        Function.support (fun ξ : ℝ => (𝓕 f) ξ) ⊆ Set.Icc (-(A : ℝ)) (A : ℝ) →
          sSup (Set.range (fun x : ℝ => ‖deriv (fun y : ℝ => f y) x‖)) ≤
            C1 * Real.rpow (A : ℝ) (3 / 2 - s) *
              dotHSeminorm s f := by
  have hs₀ : 0 ≤ s := by linarith [hs.1]
  have ht : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  refine ⟨2 * Real.pi * Real.sqrt 2, by positivity, ?_⟩
  intro A f hsupp
  let band := Icc (-(A : ℝ)) (A : ℝ)
  let g (ξ : ℝ) := ‖ξ‖ ^ s * ‖(𝓕 f) ξ‖
  have hg : Continuous g :=
    (continuous_id.norm.rpow_const (fun _ ↦ Or.inr hs₀)).mul (𝓕 f).continuous.norm
  have hg₀ (ξ : ℝ) : 0 ≤ g ξ :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg ξ) s) (norm_nonneg _)
  have hout (ξ : ℝ) (hξ : ξ ∉ band) : (𝓕 f) ξ = 0 :=
    Function.notMem_support.mp (fun h ↦ hξ (hsupp h))
  have henergy : Real.sqrt (∫ ξ in band, g ξ ^ 2) = dotHSeminorm s f := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun ξ hξ ↦ by simp [g, hout ξ hξ])]
    unfold dotHSeminorm
    congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp only [g]
    rw [mul_pow, ← Real.rpow_mul_natCast (norm_nonneg ξ), Nat.cast_ofNat, mul_comm s]
    rfl
  have hmoment : (∫ ξ : ℝ, ‖ξ‖ * ‖(𝓕 f) ξ‖) ≤
      (A : ℝ) ^ (1 - s) * (Real.sqrt (2 * A) * dotHSeminorm s f) := by
    calc
      _ = ∫ ξ in band, ‖ξ‖ * ‖(𝓕 f) ξ‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by simp [hout ξ hξ])).symm
      _ ≤ ∫ ξ in band, (A : ℝ) ^ (1 - s) * g ξ := by
        apply setIntegral_mono_on (continuous_id.norm.mul (𝓕 f).continuous.norm).integrableOn_Icc
          (continuous_const.mul hg).integrableOn_Icc measurableSet_Icc
        intro ξ hξ
        have hsplit : ‖ξ‖ ^ (1 - s) * ‖ξ‖ ^ s = ‖ξ‖ := by
          rw [← Real.rpow_add_of_nonneg (norm_nonneg ξ) ht hs₀, sub_add_cancel, Real.rpow_one]
        calc
          _ = ‖ξ‖ ^ (1 - s) * g ξ := by simp only [g, ← mul_assoc, hsplit, Pi.mul_apply, id_eq]
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (norm_nonneg ξ) (abs_le.mpr hξ) ht) (hg₀ ξ)
      _ = (A : ℝ) ^ (1 - s) * ∫ ξ in band, g ξ := integral_const_mul _ _
      _ ≤ _ := by
        rw [← henergy]
        exact mul_le_mul_of_nonneg_left (integral_le_sqrt_length_mul A g hg hg₀)
          (Real.rpow_nonneg A.coe_nonneg _)
  apply csSup_le (range_nonempty _)
  rintro _ ⟨x, rfl⟩
  calc
    _ ≤ _ := norm_deriv_le_fourier_moment f x
    _ ≤ _ := mul_le_mul_of_nonneg_left hmoment (by positivity : 0 ≤ 2 * Real.pi)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow (A : ℝ)]
      have hexp : (A : ℝ) ^ (1 - s) * (A : ℝ) ^ (1 / 2 : ℝ) = (A : ℝ) ^ (3 / 2 - s) := by
        rw [← Real.rpow_add_of_nonneg A.coe_nonneg ht (by norm_num)]
        congr 1
        ring
      rw [Real.rpow_eq_pow, ← hexp]
      ring

end MathlibExt.Analysis.Fourier.BandLimitedDerivSobolevBoundWanted
