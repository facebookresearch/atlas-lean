/-
# Points where f is not sequentially approachable form a countable set

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_63.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_63 … := by sorry` into the Batteries `theorem_wanted`
`countable_diff_setOf_exists_seq_tendsto_and_tendsto_apply`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.GraphNonAccumulationPointsCountableWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Calculus.GraphNonAccumulationPointsCountableWanted

/-- For $E \subset \mathbb{R}^n$ and $f : E \to \mathbb{R}^n$, let
\[
F = \{x \in E : \text{there is } \{x_k\}_{k=1}^\infty \subset E \setminus \{x\} \text{ with } x_k
\to x \text{ and } f(x_k) \to f(x)\}.
\]
Prove that $E \setminus F$ is at most countable.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Functions of
several variables), `benchmark/level2/ma_proofbench_l2_63.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted countable_diff_setOf_exists_seq_tendsto_and_tendsto_apply
    {n : ℕ}
    (E F : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x : EuclideanSpace ℝ (Fin n),
      x ∈ F ↔
        x ∈ E ∧
        ∃ xk : ℕ → EuclideanSpace ℝ (Fin n),
          (∀ k : ℕ, xk k ∈ E ∧ xk k ≠ x) ∧
          Filter.Tendsto xk Filter.atTop (nhds x) ∧
          Filter.Tendsto (fun k : ℕ => f (xk k)) Filter.atTop (nhds (f x))) :
    Set.Countable (E \ F)

end MathlibExt.Analysis.Calculus.GraphNonAccumulationPointsCountableWanted
