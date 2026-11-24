/-
# Nearest points to closed convex sets in reflexive Banach spaces

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_64.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_64 … := by sorry` into the Batteries `theorem_wanted`
`exists_norm_sub_eq_iInf_of_reflexive_of_convex_of_isClosed`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.ReflexiveBanachNearestPointWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ReflexiveBanachNearestPointWanted

/-- **Nearest points in reflexive Banach spaces.** Let $X$ be a reflexive complex Banach space, that
is, the canonical embedding of $X$ into its double dual is surjective, and let $C \subseteq X$ be a
nonempty closed convex set. Then for every $x_0 \in X$ there is $y_0 \in C$ such that
$\|x_0 - y_0\| = \inf_{y \in C} \|x_0 - y\|$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_64.lean`
at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_norm_sub_eq_iInf_of_reflexive_of_convex_of_isClosed
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (hX_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ X)) (C : Set X)
  (hC_closed : IsClosed C) (_hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty) :
  ∀ x₀ : X, ∃ y₀ ∈ C, ‖x₀ - y₀‖ = ⨅ y : C, ‖x₀ - (y : X)‖

end MathlibExt.Analysis.FunctionalAnalysis.ReflexiveBanachNearestPointWanted
