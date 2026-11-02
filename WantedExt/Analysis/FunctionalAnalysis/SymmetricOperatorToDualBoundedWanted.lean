/-
# A symmetric linear map from a Banach space to its dual is bounded

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_22.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_22 … := by sorry` into the Batteries `theorem_wanted`
`exists_bound_of_symmetric_linearMap_to_strongDual`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.SymmetricOperatorToDualBoundedWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.SymmetricOperatorToDualBoundedWanted

universe u

/-- **A symmetric linear map from a Banach space to its dual is bounded.** Let $E$ be a real
Banach space with dual space $E^*$ of continuous linear functionals, and let $T : E \to E^*$ be
a linear map that is symmetric: $(Tx)(y) = (Ty)(x)$ for all $x, y \in E$. Then $T$ is bounded:
there is a constant $C \ge 0$ such that $\|Tx\| \le C \|x\|$ for all $x \in E$, where $\|Tx\|$
is the operator norm of the functional $Tx$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Operator theory; General theory
of linear operators), `benchmark/level1/ma_proofbench_l1_22.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_bound_of_symmetric_linearMap_to_strongDual
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →ₗ[ℝ] StrongDual ℝ E) (hsym : ∀ x y : E, (T x) y = (T y) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖T x‖ ≤ C * ‖x‖

end MathlibExt.Analysis.FunctionalAnalysis.SymmetricOperatorToDualBoundedWanted
