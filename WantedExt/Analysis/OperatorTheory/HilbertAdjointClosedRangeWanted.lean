/-
# Closed range of an operator implies closed range of its Hilbert adjoint

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_85.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_85 … := by sorry` into the Batteries `theorem_wanted`
`isClosed_range_adjoint_of_isClosed_range`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.HilbertAdjointClosedRangeWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory Filter

namespace MathlibExt.Analysis.OperatorTheory.HilbertAdjointClosedRangeWanted

/-- **Closed range passes to the Hilbert space adjoint.** Let $X$ and $Y$ be complex Hilbert spaces
and let $A : X \to Y$ be a bounded linear operator with Hilbert space adjoint $A^* : Y \to X$. If
the range of $A$ is closed in $Y$, then the range of $A^*$ is closed in $X$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_85.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted isClosed_range_adjoint_of_isClosed_range {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (A : X →L[ℂ] Y)
    (hRan : IsClosed (LinearMap.range A.toLinearMap : Set Y)) :
    IsClosed (LinearMap.range A.adjoint.toLinearMap : Set X)

end MathlibExt.Analysis.OperatorTheory.HilbertAdjointClosedRangeWanted
