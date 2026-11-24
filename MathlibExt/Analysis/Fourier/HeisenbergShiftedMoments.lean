/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_46.lean` (openbmb/ma-proofbench, commit 31bab4c):
the problem statement, by L. Pu et al., licensed under the MIT License.

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

public import MathlibExt.Analysis.Fourier.HeisenbergUncertainty

/-!
# Heisenberg uncertainty inequality with shifted moments

The squared mass of a Schwartz function is bounded by `16 * π ^ 2` times
the product of its position and Fourier second moments about arbitrary centers.
-/

open MeasureTheory
open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.HeisenbergShiftedMomentsWanted

private theorem norm_fourier_translate (f : SchwartzMap ℝ ℂ) (a ξ : ℝ) :
    ‖(𝓕 (f.compSubConstCLM ℂ (-a))) ξ‖ = ‖(𝓕 f) ξ‖ := by
  have hcoe : ⇑(f.compSubConstCLM ℂ (-a)) = f ∘ (fun x ↦ x + a) := by
    funext x
    simp
  rw [SchwartzMap.fourier_coe, hcoe]
  exact (congrArg (fun g : ℝ → ℂ ↦ ‖g ξ‖)
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume (innerₗ ℝ) f a)).trans
    (Circle.norm_smul _ _)

private theorem integral_sq_mul_translate (w : ℝ → ℝ) (a : ℝ) :
    (∫ x : ℝ, x ^ 2 * w (x + a)) = ∫ x : ℝ, (x - a) ^ 2 * w x := by
  simpa using integral_add_right_eq_self (fun x : ℝ ↦ (x - a) ^ 2 * w x) a

/-- **Heisenberg uncertainty inequality with shifted moments.** For a complex-valued Schwartz
function $f$ on $\mathbb{R}$, write
$\hat{f}(\xi) = \int_{\mathbb{R}} f(x) e^{-2\pi i x \xi}\, dx$ for its Fourier transform. There is
a constant $C > 0$ such that for all real numbers $c$ and $d$ and every complex-valued Schwartz
function $f$ on $\mathbb{R}$,

$$
\left(\int_{\mathbb{R}} |f(x)|^2\, dx\right)^2 \le C
\left(\int_{\mathbb{R}} (x - c)^2 |f(x)|^2\, dx\right)
\left(\int_{\mathbb{R}} (\xi - d)^2 |\hat{f}(\xi)|^2\, d\xi\right).
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_46.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_const_sq_integral_sq_le_mul_shifted_moments_fourier :
    ∃ C : ℝ, 0 < C ∧
      ∀ c d : ℝ, ∀ f : SchwartzMap ℝ ℂ,
        (∫ x : ℝ, ‖f x‖ ^ 2) ^ 2 ≤
          C * (∫ x : ℝ, (x - c) ^ 2 * ‖f x‖ ^ 2) *
            (∫ ξ : ℝ, (ξ - d) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
  refine ⟨16 * Real.pi ^ 2, by positivity, ?_⟩
  intro c d f
  let g := f.compSubConstCLM ℂ (-c)
  let h := (𝓕 g).compSubConstCLM ℂ (-d)
  -- Translating the spectrum of g changes its inverse transform by a unit phase.
  have hpos (x : ℝ) : ‖(𝓕⁻ h) x‖ = ‖f (x + c)‖ := calc
    ‖(𝓕⁻ h) x‖ = ‖(𝓕⁻ (𝓕 g)) x‖ := norm_fourier_translate (𝓕 g) d (-x)
    _ = ‖f (x + c)‖ := by simp [g]
  have hfreq (ξ : ℝ) : ‖h ξ‖ = ‖(𝓕 f) (ξ + d)‖ := by
    simpa [h, g] using norm_fourier_translate f c (ξ + d)
  have bound := HeisenbergUncertainty.heisenberg_uncertainty_fourier (𝓕⁻ h)
  simp only [FourierTransform.fourier_fourierInv_eq, hpos, hfreq] at bound
  simpa only [integral_add_right_eq_self (fun x ↦ ‖f x‖ ^ 2) c,
    integral_sq_mul_translate (fun x ↦ ‖f x‖ ^ 2) c,
    integral_sq_mul_translate (fun ξ ↦ ‖(𝓕 f) ξ‖ ^ 2) d] using bound

end MathlibExt.Analysis.Fourier.HeisenbergShiftedMomentsWanted
