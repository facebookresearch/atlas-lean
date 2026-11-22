/-
# Entire function 1+Σ(z/n)^n has at most 4R zeros in |z|<R

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_91.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_91 … := by sorry` into the Batteries `theorem_wanted`
`exists_finset_zeros_sum_analyticOrderNatAt_le`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.ZerosOfSumZDivNPowNWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system; added docstrings to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.Complex.ZerosOfSumZDivNPowNWanted

/-- The entire function `F z = 1 + ∑' n, (z / (n + 1)) ^ (n + 1)`. -/
noncomputable def F : ℂ → ℂ :=
  fun z => 1 + ∑' n : ℕ, (z / (n + 1 : ℂ)) ^ (n + 1)

/-- Consider the entire function
\[
F(z)=1+\sum_{n=1}^{\infty}\left(\frac{z}{n}\right)^{n}.
\]
Show that for any $R>0$, the function $F(z)$ has no more than $4R$ zeros (counting multiplicity) in
the ball $\{z\in\mathbb{C}:\lvert z\rvert<R\}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Entire and meromorphic functions of one complex variable, and related topics),
`benchmark/level2/ma_proofbench_l2_91.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_finset_zeros_sum_analyticOrderNatAt_le
  (R : ℝ)
  (hR : 0 < R) :
  ∃ s : Finset ℂ,
    (∀ z : ℂ, z ∈ s ↔ ‖z‖ < R ∧ F z = 0) ∧
    ((∑ z ∈ s, analyticOrderNatAt F z) : ℝ) ≤ 4 * R

end MathlibExt.Analysis.Complex.ZerosOfSumZDivNPowNWanted
