/-
# Bernstein inequality for band-limited Schwartz functions

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_70.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_70 … := by sorry` into the Batteries `theorem_wanted`
`exists_norm_deriv_toLp_le_of_support_fourier_subset_ball`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.BernsteinInequalityBandLimitedWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.BernsteinInequalityBandLimitedWanted

/-- **Bernstein inequality for band-limited Schwartz functions.** For a Schwartz function
$f : \mathbb{R} \to \mathbb{C}$ write $\hat f(\xi) = \int_{\mathbb{R}} f(x) e^{-2\pi i x\xi}\,dx$
for its Fourier transform. There is a constant $C_0 > 0$ such that for every $p \in [1, \infty]$
and every Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with $\hat f(\xi) = 0$ whenever
$|\xi| \ge 1$,
$$\|f'\|_{L^p(\mathbb{R})} \le C_0 \|f\|_{L^p(\mathbb{R})}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_70.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_norm_deriv_toLp_le_of_support_fourier_subset_ball :
    ∃ C0 > 0, ∀ p : ENNReal,
      (1 : ENNReal) ≤ p  →
      ∀ f : SchwartzMap ℝ ℂ,
        Function.support (fun ξ : ℝ => (𝓕 f) ξ) ⊆ Metric.ball (0 : ℝ) 1 →
          ‖(SchwartzMap.derivCLM ℂ ℂ f).toLp p
              (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ ≤
            C0 * ‖f.toLp p (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖

end MathlibExt.Analysis.Fourier.BernsteinInequalityBandLimitedWanted
