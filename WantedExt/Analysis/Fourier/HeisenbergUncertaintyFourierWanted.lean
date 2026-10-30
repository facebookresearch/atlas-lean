/-
# Heisenberg uncertainty principle with constant 1/(16π²)

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_57.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_57 … := by sorry` into the Batteries `theorem_wanted`
`integral_sq_mul_norm_sq_mul_integral_sq_mul_norm_fourier_sq_ge`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.HeisenbergUncertaintyFourierWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; changed the statement to reuse Mathlib API:
replaced the source's helper `schwartzFourierHat ψ ξ = ∫ ψ x * exp (-2πi x ξ)` by Mathlib's
Fourier transform `𝓕 ψ`, which has the same normalization
(`Real.fourier_real_eq_integral_exp_smul`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.HeisenbergUncertaintyFourierWanted

/-- Denote by $\mathcal{S}(\mathbb{R})$ the Schwartz space on $\mathbb{R}$ consisting of all
complex-valued $C^\infty$ functions $f(x)$ on $\mathbb{R}$ such that
\[
\sup_{x\in\mathbb{R}} |x|^k \left|\frac{d^\ell f}{dx^\ell}(x)\right| < \infty
\quad\text{for all } k,\ell\in\mathbb{N}\cup\{0\}.
\]
Suppose $\psi(x)\in\mathcal{S}(\mathbb{R})$ satisfies
\[
\int_{-\infty}^{\infty}|\psi(x)|^2\,dx=1.
\]
Denote by $\hat{\psi}(\xi)$ the Fourier transform of $\psi(x)$ defined by
\[
\hat{\psi}(\xi)=\int_{-\infty}^{\infty}\psi(x)e^{-2\pi i x\xi}\,dx.
\]
Prove the Fourier-transform version of the Heisenberg uncertainty principle
\[
\left(\int_{-\infty}^{\infty} x^2|\psi(x)|^2\,dx\right)
\left(\int_{-\infty}^{\infty} \xi^2|\hat{\psi}(\xi)|^2\,d\xi\right)
\ge \frac{1}{16\pi^2}.
\]

Lean variant: the Fourier transform is Mathlib's `𝓕`, which has the source's normalization `∫ ψ(x)
e^{-2πixξ} dx`, instead of the source's helper definition.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_57.lean` at openbmb/ma-proofbench@31bab4c, with the change
above.
-/
public theorem_wanted integral_sq_mul_norm_sq_mul_integral_sq_mul_norm_fourier_sq_ge
    (ψ : SchwartzMap ℝ ℂ)
    (hL2 : (∫ x : ℝ, ‖ψ x‖ ^ 2) = 1) :
    ( (∫ x : ℝ, (x ^ 2) * (‖ψ x‖ ^ 2)) *
        (∫ ξ : ℝ, (ξ ^ 2) * (‖𝓕 (⇑ψ) ξ‖ ^ 2)) )
      ≥ 1 / (16 * Real.pi ^ 2)

end MathlibExt.Analysis.Fourier.HeisenbergUncertaintyFourierWanted
