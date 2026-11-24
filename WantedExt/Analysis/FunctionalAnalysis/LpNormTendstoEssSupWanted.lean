/-
# The L^p norm tends to the L^∞ norm as p → ∞

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_42.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_42 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_eLpNorm_atTop_eLpNorm_top_of_isFiniteMeasure`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.LpNormTendstoEssSupWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory ENNReal Filter Topology

namespace MathlibExt.Analysis.FunctionalAnalysis.LpNormTendstoEssSupWanted

/-- **The $L^p$ norm tends to the $L^\infty$ norm.** Let $\mu$ be a finite measure on a measurable
space $\alpha$ and let $f \colon \alpha \to \mathbb{R}$ be essentially bounded,
$f \in L^\infty(\mu)$. Then $\|f\|_{L^p(\mu)} \to \|f\|_{L^\infty(\mu)}$ as the real exponent
$p$ tends to $\infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_42.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_eLpNorm_atTop_eLpNorm_top_of_isFiniteMeasure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hmu : μ Set.univ < ∞) {f : α → ℝ} (hf : MemLp f ∞ μ) :
    Tendsto (fun p : NNReal => eLpNorm f p μ) atTop
      (𝓝 (eLpNorm f ∞ μ))

end MathlibExt.Analysis.FunctionalAnalysis.LpNormTendstoEssSupWanted
