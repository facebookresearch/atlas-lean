/-
# Young's L^1 * L^p convolution inequality is sharp

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_45.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_45 … := by sorry` into the Batteries `theorem_wanted`
`exists_eLpNorm_convolution_gt_one_sub_mul`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.YoungConvolutionSharpWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory Convolution

namespace MathlibExt.Analysis.FunctionalAnalysis.YoungConvolutionSharpWanted

/-- Suppose $1\le p\le\infty$, $f\in L^1(R^1)$, and $g\in L^p(R^1)$. Assume $\varepsilon>0$, show
that there exist $f\in L^1(R^1)$ and $g\in L^p(R^1)$ such that

\[
\|f*g\|_p>(1-\varepsilon)\|f\|_1\|g\|_p.
\]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_45.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_eLpNorm_convolution_gt_one_sub_mul
    (p : ENNReal) (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f g : ℝ → ℝ), MemLp f 1 ∧ MemLp g p ∧
      (eLpNorm (f ⋆ g) p).toReal > ((1 - ε) * (eLpNorm f 1).toReal * (eLpNorm g p).toReal)

end MathlibExt.Analysis.FunctionalAnalysis.YoungConvolutionSharpWanted
