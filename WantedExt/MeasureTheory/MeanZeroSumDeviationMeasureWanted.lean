/-
# Large deviations of mean-zero sums on the cube have vanishing measure

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_06.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_06 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_volume_abs_sum_ge_mul_sqrt`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.MeasureTheory.MeanZeroSumDeviationMeasureWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators

namespace MathlibExt.MeasureTheory.MeanZeroSumDeviationMeasureWanted

/-- Suppose that $f\in L^{2}([0,1])$, $\int_{0}^{1} f = 0$, and $\int_{0}^{1} |f|^{2} > 0$.
Let $a_n$ be a sequence of positive numbers that converges to $\infty$. Consider
 \[
F_n=\left\{(x_1,\dots,x_n)\in [0,1]^n:\ \left|\sum_{j=1}^{n} f(x_j)\right|\ge a_n n^{1/2}\right\}.
 \]
Prove that $\lim_{n\to\infty} m_n(F_n)=0$, where $m_n$ is the Lebesgue measure on $\mathbb{R}^n$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_06.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_volume_abs_sum_ge_mul_sqrt (f : ℝ → ℝ) (a : ℕ → ℝ)
    (hf_L2 : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hf_mean_zero : ∫ x, f x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0)
    (hf_sq_pos : 0 < ∫ x, |f x| ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
    (ha_pos : ∀ n, 0 < a n)
    (ha_tendsto : Filter.Tendsto a Filter.atTop Filter.atTop)
    (F : ∀ n : ℕ, Set (Fin n → ℝ))
    (hF : ∀ n x, x ∈ F n ↔
      (∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1) ∧
      a n * Real.sqrt n ≤ |∑ i : Fin n, f (x i)|) :
    Filter.Tendsto (fun n => volume (F n)) Filter.atTop (nhds 0)

end MathlibExt.MeasureTheory.MeanZeroSumDeviationMeasureWanted
