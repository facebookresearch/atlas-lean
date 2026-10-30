/-
# d and d/(1+d) induce the same neighbourhoods

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_65.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_65 … := by sorry` into the Batteries `theorem_wanted`
`dist_div_one_add_dist_balls_equivalent`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.BoundedMetricTopologicallyEquivalentWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system; corrected the statement:
added the metric axioms of `δ` (identity of indiscernibles, symmetry, triangle inequality) as a
first conjunct; the source statement asserted only that the two families of balls are nested,
which omits the claim that `δ` is a metric.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.BoundedMetricTopologicallyEquivalentWanted

/-- Let $(X,d)$ be a metric space and define

\[
\delta(x,y):=\frac{d(x,y)}{1+d(x,y)}, \qquad x,y\in X.
\]
Prove that $d$ and $\delta$ are equivalent metrics on $X$.

Lean variant: the source statement asserts only that `d`-balls and `δ`-balls are mutually nested,
which omits the claim that `δ` is a metric; the metric axioms of `δ` are added as a first conjunct.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Inequalities in
real analysis), `benchmark/level1/ma_proofbench_l1_65.lean` at openbmb/ma-proofbench@31bab4c,
with the change above.
-/
public theorem_wanted dist_div_one_add_dist_balls_equivalent {X : Type*} [MetricSpace X]
    (δ : X → X → ℝ) (hδ : ∀ x y : X, δ x y = dist x y / (1 + dist x y)) :
    ((∀ x y : X, δ x y = 0 ↔ x = y) ∧ (∀ x y : X, δ x y = δ y x) ∧
      (∀ x y z : X, δ x z ≤ δ x y + δ y z)) ∧
    (∀ x : X, ∀ ε > 0, ∃ η > 0, Metric.ball x η ⊆ {y : X | δ x y < ε}) ∧
    (∀ x : X, ∀ ε > 0, ∃ η > 0, {y : X | δ x y < η} ⊆ Metric.ball x ε)

end MathlibExt.Analysis.FunctionalAnalysis.BoundedMetricTopologicallyEquivalentWanted
