/-
# Convexity iff the first-order tangent inequality

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_95.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_95 … := by sorry` into the Batteries `theorem_wanted`
`convexOn_iff_forall_le_add_fderivWithin`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.ConvexOnIffAboveTangentWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ConvexOnIffAboveTangentWanted

/-- Suppose $X$ is an open convex subset of a Banach space $E$ and $f\in C^2(X,\mathbb R)$. Show
these statements are equivalent:

$f$ is convex;
$f(x)\ge f(a)+\partial f(a)(x-a)$, for $a,x\in X$;

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Measures,
integration, derivative, holomorphy), `benchmark/level1/ma_proofbench_l1_95.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted convexOn_iff_forall_le_add_fderivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : Set E} (hXopen : IsOpen X) (hXconv : Convex ℝ X)
    {f : E → ℝ} (hf : ContDiffOn ℝ 2 f X) :
    ConvexOn ℝ X f ↔
      ∀ ⦃a⦄, a ∈ X → ∀ ⦃x⦄, x ∈ X →
        f x ≥ f a + (fderivWithin ℝ f X a) (x - a)

end MathlibExt.Analysis.FunctionalAnalysis.ConvexOnIffAboveTangentWanted
