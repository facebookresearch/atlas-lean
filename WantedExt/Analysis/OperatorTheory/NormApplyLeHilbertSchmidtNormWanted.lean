/-
# ‖Tx‖ is bounded by the Hilbert-Schmidt norm on unit vectors

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_68.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_68 … := by sorry` into the Batteries `theorem_wanted`
`norm_apply_le_hsNorm_of_norm_eq_one`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.NormApplyLeHilbertSchmidtNormWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions; replaced the real-valued helper `hsNorm` (which is `0` when the defining series
diverges) by the shared `ℝ≥0∞`-valued `HilbertSchmidtNorm.hsENNNorm` and dropped the
divergence disjunct from the conclusion (with the extended-valued norm the bound holds as
stated, trivially when the Hilbert–Schmidt norm is `⊤`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib
public import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.OperatorTheory.NormApplyLeHilbertSchmidtNormWanted

/-- **The Hilbert–Schmidt norm bounds an operator on unit vectors.** Let $H$ be a real Hilbert
space, let $T : H \to H$ be a bounded linear operator, and let $(u_n)_{n \in \mathbb{N}}$ be an
orthonormal basis of $H$ indexed by the natural numbers. Let
$\|T\|_{\mathrm{HS}} = \bigl(\sum_{n} \|T u_n\|^2\bigr)^{1/2} \in [0, \infty]$ be the
Hilbert–Schmidt norm of $T$ computed in this basis; it is $\infty$ when the series diverges.
Then $\|Tx\| \le \|T\|_{\mathrm{HS}}$ for every $x \in H$ with $\|x\| = 1$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Special
classes of linear operators), `benchmark/level2/ma_proofbench_l2_68.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted norm_apply_le_hsNorm_of_norm_eq_one
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H)
    (u : HilbertBasis ℕ ℝ H) :
    ∀ x : H, ‖x‖ = 1 → ENNReal.ofReal ‖T x‖ ≤ HilbertSchmidtNorm.hsENNNorm T u

end MathlibExt.Analysis.OperatorTheory.NormApplyLeHilbertSchmidtNormWanted
