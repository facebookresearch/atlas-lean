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

/-- **Fourier solution of the Airy equation.** For $u_0 : \mathbb{R} \to \mathbb{C}$, let
$\widehat{u_0}(\xi) = (2\pi)^{-1/2} \int_{\mathbb{R}} u_0(y) e^{-iy\xi}\,dy$ be its unitary
Fourier transform. The Airy solution with initial datum $u_0$ is the function
$u : \mathbb{R}^2 \to \mathbb{C}$ given by
$$u(t, x) = (2\pi)^{-1/2} \int_{\mathbb{R}} e^{i(t\xi^3 + x\xi)}\, \widehat{u_0}(\xi)\,d\xi,$$
where an integral whose integrand is not integrable is taken to be $0$.

For $u_0 \in C_c^\infty(\mathbb{R})$ this function solves the Airy equation
$\partial_t u + \partial_x^3 u = 0$ with $u(0, \cdot) = u_0$. -/
noncomputable def AirySolution (u0 : ℝ → ℂ) (t x : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi))⁻¹ *
    ∫ ξ : ℝ,
      Complex.exp (Complex.I * (t * ξ ^ (3 : ℕ) + x * ξ)) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * (𝓕 u0) (ξ / (2 * Real.pi)))

/-- **Kato smoothing identity for the Airy equation.** For $u_0 : \mathbb{R} \to \mathbb{C}$ let
$\widehat{u_0}(\xi) = (2\pi)^{-1/2} \int_{\mathbb{R}} u_0(y) e^{-iy\xi}\,dy$ be its unitary
Fourier transform, and let
$u(t, x) = (2\pi)^{-1/2} \int_{\mathbb{R}} e^{i(t\xi^3 + x\xi)}\, \widehat{u_0}(\xi)\,d\xi$ be
the Airy solution with initial datum $u_0$. There is a constant $c_0 > 0$ such that for every
smooth compactly supported $u_0 : \mathbb{R} \to \mathbb{C}$ and every $x_0 \in \mathbb{R}$, the
function $t \mapsto \partial_x u(t, x_0)$ belongs to $L^2(\mathbb{R})$ and
$$\int_{\mathbb{R}} |\partial_x u(t, x_0)|^2\,dt = c_0 \int_{\mathbb{R}} |u_0(x)|^2\,dx.$$

The source's formalization used the transform $\int u_0(y) e^{-2\pi i y\xi}\,dy$ together with
the unitary phase and prefactor, so its initial datum was not $u_0$ but the $L^2$-isometric
rescaling $x \mapsto (2\pi)^{-1/2} u_0(x / 2\pi)$; the identity holds for both with the same
$c_0$.

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
