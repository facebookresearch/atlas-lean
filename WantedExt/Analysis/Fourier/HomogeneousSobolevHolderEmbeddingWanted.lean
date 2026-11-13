/-
# Homogeneous H^s seminorm controls the C^(s-1/2) Holder seminorm

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_21.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_21 … := by sorry` into the Batteries `theorem_wanted`
`exists_holderSeminorm_le_mul_dotHSeminorm`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.HomogeneousSobolevHolderEmbeddingWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system; added docstrings to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.HomogeneousSobolevHolderEmbeddingWanted

/-- **Homogeneous Sobolev seminorm for the Hölder embedding.** For a real number $s$ and a
Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with Fourier transform
$\hat f(\xi) = \int_{\mathbb{R}} e^{-2\pi i x \xi} f(x) \, dx$, the homogeneous Sobolev seminorm
of $f$ is
$$
\|f\|_{\dot H^s} = \left( \int_{\mathbb{R}} |\xi|^{2s} \, |\hat f(\xi)|^2 \, d\xi \right)^{1/2},
$$
where the integral is taken to be $0$ when the integrand is not integrable. -/
noncomputable def dotHSeminorm (s : ℝ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  Real.sqrt (∫ ξ : ℝ, Real.rpow ‖ξ‖ (2 * s) * ‖(𝓕 f) ξ‖ ^ 2)

/-- **The homogeneous Sobolev seminorm controls the Hölder seminorm.** Let $s \in (\tfrac12, 1]$,
and for a Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with Fourier transform $\hat f$ let
$\|f\|_{\dot H^s} = \left( \int_{\mathbb{R}} |\xi|^{2s} |\hat f(\xi)|^2 \, d\xi \right)^{1/2}$
be its homogeneous Sobolev seminorm. There is a constant $C_3 > 0$ such that for every Schwartz
function $f : \mathbb{R} \to \mathbb{C}$,
$$
\sup_{x \ne y} \frac{|f(x) - f(y)|}{|x - y|^{s - \frac12}} \le C_3 \, \|f\|_{\dot H^s}.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_21.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_holderSeminorm_le_mul_dotHSeminorm
    (s : ℝ) (hs : s ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    ∃ C3 > 0, ∀ f : SchwartzMap ℝ ℂ,
      sSup
          (Set.range
            (fun p : {xy : ℝ × ℝ // xy.1 ≠ xy.2} =>
              ‖f p.1.1 - f p.1.2‖ / Real.rpow ‖p.1.1 - p.1.2‖ (s - 1 / 2)))
        ≤ C3 * dotHSeminorm s f

end MathlibExt.Analysis.Fourier.HomogeneousSobolevHolderEmbeddingWanted
