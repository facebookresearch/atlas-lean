/-
# 1 / sum (a_k + 1/a_k) tends to zero

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_18.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_18 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_one_div_sum_add_inv_zero`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.Analysis.SpecificLimits.ReciprocalSumAddInvNullWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added docstrings to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Filter Topology

namespace MathlibExt.Analysis.SpecificLimits.ReciprocalSumAddInvNullWanted

/-- **Partial sums of $a_k + 1/a_k$.** For a real sequence $(a_k)_{k \in \mathbb{N}}$, the sequence
$(x_n)_{n \in \mathbb{N}}$ is given by $x_n = \sum_{k=0}^{n} (a_k + 1/a_k)$ for $n \in \mathbb{N}$,
with the convention $1/0 = 0$. -/
noncomputable def xSeq (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n ↦ ∑ k ∈ Finset.range (n + 1), (a k + (1 / a k))

/-- **The reciprocals of $\sum_{k=0}^{n} (a_k + 1/a_k)$ tend to zero.** Let
$(a_n)_{n \in \mathbb{N}}$ be a sequence of positive real numbers, and for $n \in \mathbb{N}$ let
$x_n = \sum_{k=0}^{n} (a_k + 1/a_k)$. Then $1/x_n \to 0$ as $n \to \infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Sequences, series, summability;
Convergence and divergence of infinite limiting processes),
`benchmark/level1/ma_proofbench_l1_18.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_one_div_sum_add_inv_zero (a : ℕ → ℝ) (ha : ∀ n : ℕ, 0 < a n) :
    Tendsto (fun n ↦ 1 / xSeq a n) atTop (𝓝 0)

end MathlibExt.Analysis.SpecificLimits.ReciprocalSumAddInvNullWanted
