/-
# 0 < e − Σ_{k≤n} 1/k! < 1/(n·n!)

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_73.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_73 … := by sorry` into the Batteries `theorem_wanted`
`exp_one_sub_sum_inv_factorial_pos_and_lt`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.SpecificLimits.ExpOneTaylorRemainderBoundWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.SpecificLimits.ExpOneTaylorRemainderBoundWanted

/-- **Error bound for the partial sums of the series for $e$.** For every integer $n \ge 1$,

$$0 < e - \sum_{k=0}^{n} \frac{1}{k!} < \frac{1}{n \cdot n!}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_73.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exp_one_sub_sum_inv_factorial_pos_and_lt (n : ℕ) (hn : 0 < n) :
    0 < Real.exp 1 - (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (Nat.factorial k)) ∧
    Real.exp 1 - (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (Nat.factorial k)) <
      (1 : ℝ) / (n * Nat.factorial n)

end MathlibExt.Analysis.SpecificLimits.ExpOneTaylorRemainderBoundWanted
