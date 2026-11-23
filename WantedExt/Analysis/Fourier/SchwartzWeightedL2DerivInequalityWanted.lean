/-
# ‖f‖₂² ≤ 2‖xf‖₂‖f'‖₂ for real Schwartz functions

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_40.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_40 … := by sorry` into the Batteries `theorem_wanted`
`integral_sq_le_two_mul_sqrt_integral_mul_sq_mul_sqrt_integral_deriv_sq`; moved the informal
problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.SchwartzWeightedL2DerivInequalityWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Fourier.SchwartzWeightedL2DerivInequalityWanted

/-- **Weighted $L^2$ inequality for real Schwartz functions.** For every real-valued Schwartz
function $f : \mathbb{R} \to \mathbb{R}$,
$$
\int_{\mathbb{R}} f(x)^2 \, dx \le 2 \left( \int_{\mathbb{R}} x^2 f(x)^2 \, dx \right)^{1/2}
\left( \int_{\mathbb{R}} f'(x)^2 \, dx \right)^{1/2},
$$
that is, $\|f\|_{L^2}^2 \le 2 \, \|x f\|_{L^2} \, \|f'\|_{L^2}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_40.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted integral_sq_le_two_mul_sqrt_integral_mul_sq_mul_sqrt_integral_deriv_sq
    (f : SchwartzMap ℝ ℝ) :
    (∫ x : ℝ, ‖f x‖ ^ 2) ≤
      2 * Real.sqrt (∫ x : ℝ, ‖x * f x‖ ^ 2) *
        Real.sqrt (∫ x : ℝ, ‖deriv (fun y : ℝ => f y) x‖ ^ 2)

end MathlibExt.Analysis.Fourier.SchwartzWeightedL2DerivInequalityWanted
