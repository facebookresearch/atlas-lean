/-
# If T*T is Fredholm then T has closed range

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_23.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_23 … := by sorry` into the Batteries `theorem_wanted`
`isClosed_range_of_isFredholm_adjoint_comp`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.AdjointCompFredholmClosedRangeWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; changed the statement to reuse
Mathlib API: replaced the source's helper predicate `IsFredholm` (finite-dimensional kernel and
a finite-dimensional complement of the range) by Mathlib's `ContinuousLinearMap.IsFredholm`,
which also records closed range, strictness, and a complemented kernel; for bounded operators
between Hilbert spaces these follow from the source's two conditions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.OperatorTheory.AdjointCompFredholmClosedRangeWanted

/-- **Closed range from a Fredholm $T^*T$.** Let $X$ and $Y$ be complex Hilbert spaces and let
$T : X \to Y$ be a bounded linear operator with Hilbert space adjoint $T^* : Y \to X$. If
$T^*T : X \to X$ is a Fredholm operator, then the range of $T$ is closed in $Y$.

Here a Fredholm operator is a bounded linear operator that is open onto its range, whose range is
closed and of finite codimension, and whose kernel is finite-dimensional and has a closed
complement. The source asks only for a finite-dimensional kernel and a range of finite
codimension; between Hilbert spaces the two agree, since a finite-codimensional range of a bounded
operator is closed.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_23.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
public theorem_wanted isClosed_range_of_isFredholm_adjoint_comp {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (T : X →L[ℂ] Y)
    (hFredholm : (ContinuousLinearMap.adjoint T ∘L T).IsFredholm) :
    IsClosed (LinearMap.range T.toLinearMap : Set Y)

end MathlibExt.Analysis.OperatorTheory.AdjointCompFredholmClosedRangeWanted
