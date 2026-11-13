/-
# Hilbert–Schmidt norm of a finite-rank operator bounded by its op norm

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_98.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_98 … := by sorry` into the Batteries `theorem_wanted`
`exists_hsNorm_le_mul_opNorm_of_finiteDimensional_quotient_ker`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.HilbertSchmidtFiniteRankBoundWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions; replaced the real-valued helper `hsNorm` (which is `0` when the defining series
diverges) by the shared `ℝ≥0∞`-valued `HilbertSchmidtNorm.hsENNNorm`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib
public import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.OperatorTheory.HilbertSchmidtFiniteRankBoundWanted

/-- **The Hilbert–Schmidt norm of a finite-rank operator is controlled by its operator norm.**
There is a function $C$ from the natural numbers to the positive reals with the following
property. Let $H$ be an infinite-dimensional separable real Hilbert space, let
$(u_i)_{i \in \mathbb{N}}$ be a Hilbert basis of $H$, and let $T : H \to H$ be a bounded linear
operator such that the quotient $H/\ker T$ is finite-dimensional, of dimension $n$. Then the
Hilbert–Schmidt norm of $T$ computed in the basis $(u_i)$, taken in $[0,\infty]$, satisfies
$$\Big(\sum_{i \in \mathbb{N}} \|Tu_i\|^2\Big)^{1/2} \le C(n)\,\|T\|,$$
where $\|T\|$ is the operator norm of $T$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_98.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_hsNorm_le_mul_opNorm_of_finiteDimensional_quotient_ker :
    ∃ C : ℕ → ℝ, (∀ n : ℕ, 0 < C n) ∧
      ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [TopologicalSpace.SeparableSpace H] (hH : ¬ FiniteDimensional ℝ H)
        (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
        [FiniteDimensional ℝ (H ⧸ T.ker)],
        HilbertSchmidtNorm.hsENNNorm T (⇑b) ≤
          ENNReal.ofReal (C (Module.finrank ℝ (H ⧸ T.ker)) * ‖T‖)

end MathlibExt.Analysis.OperatorTheory.HilbertSchmidtFiniteRankBoundWanted
