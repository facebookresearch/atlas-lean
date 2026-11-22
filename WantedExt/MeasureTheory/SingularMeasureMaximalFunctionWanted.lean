/-
# Maximal function of a singular measure is infinite μ-a.e.

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_44.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_44 … := by sorry` into the Batteries `theorem_wanted`
`measure_setOf_maximalFunction_lt_top_eq_zero_of_mutuallySingular`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.SingularMeasureMaximalFunctionWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.MeasureTheory.SingularMeasureMaximalFunctionWanted

/-- Let $\mu$ be a Borel measure on $\mathbb{R}^n$. Suppose that $\mu$ is singular with respect to
the Lebesgue measure $m_n$ and define
\[
M_\mu(x) = \sup_{r>0} \frac{\mu(B(x, r))}{m_n(B(x, r))}.
\]
Prove that $\mu\{x : M_\mu(x) < \infty\} = 0$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_44.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted measure_setOf_maximalFunction_lt_top_eq_zero_of_mutuallySingular
    {n : ℕ}
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    (hsing : MeasureTheory.Measure.MutuallySingular μ MeasureTheory.volume)
    (Mmu : EuclideanSpace ℝ (Fin n) → ENNReal)
    (hMdef : ∀ x : EuclideanSpace ℝ (Fin n),
      Mmu x = ⨆ (r : ℝ) (_ : 0 < r),
        μ (Metric.ball x r) / MeasureTheory.volume (Metric.ball x r)) :
    μ {x : EuclideanSpace ℝ (Fin n) | Mmu x < ⊤} = 0

end MathlibExt.MeasureTheory.SingularMeasureMaximalFunctionWanted
