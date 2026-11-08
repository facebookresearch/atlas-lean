/-
# Bounded a.e.-null sequences in L^p converge weakly to 0

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_10.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_10 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_integral_mul_of_ae_tendsto_zero_of_eLpNorm_le_one`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory Filter

namespace MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted

/-- Lebesgue measure restricted to `(0, 1)`. -/
noncomputable abbrev μI01 : Measure ℝ := Measure.restrict volume (Set.Ioo (0 : ℝ) 1)

/-- Let $p\in(1,+\infty)$. Suppose that $(f_n)_n \subset L^{p}(0,1)$ and $\|f_n\|_{L^{p}}\le 1$ for
all $n$. Assuming that $f_n(x)\to 0$ a.e., prove that $(f_n)_n$ converges weakly to $0$ in
$L^{p}(0,1)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_10.lean`
at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_integral_mul_of_ae_tendsto_zero_of_eLpNorm_le_one
  (p q : ENNReal)
  (hp_ne_top : p ≠ ⊤)
  (hp_gt_one : 1 < p)
  (hq : 1 / p + 1 / q = 1)
  (f : ℕ → Lp ℝ p μI01)
  (h_bound : ∀ n, eLpNorm (f n) p μI01 ≤ 1)
  (h_ae : ∀ᵐ x ∂μI01, Tendsto (fun n => f n x) atTop (nhds 0)) :
  ∀ g : Lp ℝ q μI01, Tendsto (fun n => ∫ x, (f n x) * g x ∂μI01) atTop (nhds 0)

end MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted
