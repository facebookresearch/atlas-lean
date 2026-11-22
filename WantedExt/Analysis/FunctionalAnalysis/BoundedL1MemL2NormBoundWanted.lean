/-
# A bounded L^1 function on R^d is L^2 with an interpolation bound

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_41.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_41 … := by sorry` into the Batteries `theorem_wanted`
`memLp_two_and_eLpNorm_two_le_of_bounded_of_memLp_one`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.BoundedL1MemL2NormBoundWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.BoundedL1MemL2NormBoundWanted

/-- **A bounded integrable function is square integrable.** Let $d$ be a natural number, let
$M \ge 0$, and let $f \colon \mathbb{R}^d \to \mathbb{R}$ satisfy $|f(x)| \le M$ for every
$x \in \mathbb{R}^d$. If $f \in L^1(\mathbb{R}^d)$, then $f \in L^2(\mathbb{R}^d)$ and

$$\|f\|_{L^2(\mathbb{R}^d)} \le M^{1/2} \, \|f\|_{L^1(\mathbb{R}^d)}^{1/2},$$

where the spaces and norms are taken with respect to Lebesgue measure.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_41.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted memLp_two_and_eLpNorm_two_le_of_bounded_of_memLp_one
    (d : ℕ) (f : (Fin d → ℝ) → ℝ) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x, ‖f x‖ ≤ M)
    (hf : MeasureTheory.MemLp f 1) :
    (MeasureTheory.MemLp f 2) ∧
      (MeasureTheory.eLpNorm f 2).toReal ≤
        Real.sqrt M * Real.sqrt (MeasureTheory.eLpNorm f 1).toReal

end MathlibExt.Analysis.FunctionalAnalysis.BoundedL1MemL2NormBoundWanted
