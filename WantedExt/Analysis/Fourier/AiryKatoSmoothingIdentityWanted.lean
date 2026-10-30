/-
# Kato smoothing identity for the Airy equation

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

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_27.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_27 … := by sorry` into the Batteries `theorem_wanted`
`exists_pos_const_integral_norm_deriv_airySolution_sq_eq`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.AiryKatoSmoothingIdentityWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added docstrings to helper definitions;
corrected the statement: the source's helper `AirySolution` paired Mathlib's `𝓕` (convention `∫
u₀ y * exp (-2πi y ξ) dy`) with the unitary convention's phase `exp (i x ξ)` and prefactor `(2π)
^ (-1 / 2)`, so its value at `t = 0` was `(2π) ^ (-1 / 2) * u₀ (x / (2π))` rather than `u₀ x`;
the helper now uses the unitary transform `(2π) ^ (-1 / 2) * 𝓕 u₀ (ξ / (2π))`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory
open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.AiryKatoSmoothingIdentityWanted

/-- `u(t, x) = (2π) ^ (-1 / 2) * ∫ exp (i (t ξ ^ 3 + x ξ)) * û₀ ξ dξ`, where `û₀ ξ = (2π) ^ (-1 / 2)
* 𝓕 u₀ (ξ / (2π)) = (2π) ^ (-1 / 2) * ∫ u₀ y * exp (-i y ξ) dy` is the unitary Fourier transform:
the solution of the Airy equation with initial datum `u₀`. -/
noncomputable def AirySolution (u0 : ℝ → ℂ) (t x : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi))⁻¹ *
    ∫ ξ : ℝ,
      Complex.exp (Complex.I * (t * ξ ^ (3 : ℕ) + x * ξ)) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * (𝓕 u0) (ξ / (2 * Real.pi)))

/-- For all $u_0\in C_c^\infty(\mathbb{R})$, we define $u(t,x)\in C^\infty(\mathbb{R}^2)$ as follows
\[
u(t,x)=\frac{1}{\sqrt{2\pi}}\int_{\mathbb{R}} e^{i(t\xi^3+x\xi)}\widehat{u_0}(\xi)\,d\xi.
\]
Show that for all $x_0\in\mathbb{R}$, the function $t\mapsto \partial_x u(t,x_0)$ belongs to
$L^2(\mathbb{R})$ and there exists a constant $c_0>0$ independent of $x_0$ and $u$, such that
\[
\int_{\mathbb{R}} |\partial_x u(t,x_0)|^2\,dt = c_0 \int_{\mathbb{R}} |u_0(x)|^2\,dx.
\]

Lean variant: the source's helper used Mathlib's `𝓕`, whose convention is `∫ u₀(y) e^{-2πiyξ} dy`,
together with the unitary convention's phase and prefactor, so its initial datum was not `u₀`;
`AirySolution` now uses the unitary transform `(2π)^{-1/2} 𝓕 u₀ (ξ / 2π)`. The two initial data
differ by an L²-isometric rescaling, so the identity holds for both with the same `c₀`.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_27.lean` at openbmb/ma-proofbench@31bab4c, with the change
above.
-/
public theorem_wanted exists_pos_const_integral_norm_deriv_airySolution_sq_eq :
  ∃ c0 : ℝ, 0 < c0 ∧
    ∀ (u0 : ℝ → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) u0 →
      HasCompactSupport u0 →
      (∀ x0 : ℝ,
          MemLp (fun t : ℝ => deriv (fun x : ℝ => AirySolution u0 t x) x0)
            (2 : ENNReal) volume) ∧
        ∀ x0 : ℝ,
          ∫ t : ℝ, ‖deriv (fun x : ℝ => AirySolution u0 t x) x0‖ ^ (2 : ℕ) =
            c0 * ∫ x : ℝ, ‖u0 x‖ ^ (2 : ℕ)

end MathlibExt.Analysis.Fourier.AiryKatoSmoothingIdentityWanted
