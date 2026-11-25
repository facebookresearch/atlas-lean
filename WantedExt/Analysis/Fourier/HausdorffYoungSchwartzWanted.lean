/-
# Hausdorff–Young inequality for Schwartz functions on ℝ^n

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_84.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_84 … := by sorry` into the Batteries `theorem_wanted`
`exists_norm_fourier_toLp_le_norm_toLp_of_holderConjugate`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.HausdorffYoungSchwartzWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.HausdorffYoungSchwartzWanted

/-- **Hausdorff–Young inequality for Schwartz functions.** Let $n$ be a natural number and let
$\mathcal{F}$ be the Fourier transform on $\mathbb{R}^n$,
$\mathcal{F}f(\xi) = \int_{\mathbb{R}^n} f(x) e^{-2\pi i \langle x, \xi \rangle}\, dx$. There is a
constant $C > 0$ such that for all $p, p' \in [0, \infty]$ with $1 \le p \le 2$ and
$\frac{1}{p} + \frac{1}{p'} = 1$ (so $p' = \infty$ when $p = 1$) and every complex-valued
Schwartz function $f$ on $\mathbb{R}^n$, $\|\mathcal{F}f\|_{L^{p'}} \le C \|f\|_{L^p}$, where the
$L^p$ norms are taken with respect to Lebesgue measure on $\mathbb{R}^n$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_84.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_norm_fourier_toLp_le_norm_toLp_of_holderConjugate
    {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ p p' : ENNReal,
        1 ≤ p → p ≤ 2 → ENNReal.HolderConjugate p p' →
          ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
            ‖(𝓕 f).toLp p'
                (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))‖ ≤
              C * ‖f.toLp p
                (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))‖

end MathlibExt.Analysis.Fourier.HausdorffYoungSchwartzWanted
