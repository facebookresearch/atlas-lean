/-
# Power series agreeing at 1/2, 1/3, ... have equal coefficients

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_24.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_24 … := by sorry` into the Batteries `theorem_wanted`
`coeff_eq_of_tsum_eq_on_inv_nat_add_two`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.SpecificLimits.PowerSeriesCoeffEqOfAgreeOnReciprocalsWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.SpecificLimits.PowerSeriesCoeffEqOfAgreeOnReciprocalsWanted

/-- Let $\sum_{k=0}^{\infty}a_k x^k$ and $\sum_{k=0}^{\infty}b_k x^k$ be real power series which
converge for $|x|<1$.

Suppose that $\sum_{k=0}^{\infty}a_k x^k=\sum_{k=0}^{\infty}b_k x^k$ when $x=1/2,1/3,1/4,\dots$.
Prove that $a_k=b_k$ for all $k$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_24.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted coeff_eq_of_tsum_eq_on_inv_nat_add_two
    (a b : ℕ → ℝ) (ha : ∀ x : ℝ, |x| < 1 → Summable (fun k : ℕ => a k * x ^ k))
    (hb : ∀ x : ℝ, |x| < 1 → Summable (fun k : ℕ => b k * x ^ k))
    (hEq : ∀ n : ℕ, (∑' k : ℕ, a k * ((1 : ℝ) / (n + 2)) ^ k) =
      (∑' k : ℕ, b k * ((1 : ℝ) / (n + 2)) ^ k)) :
    ∀ k : ℕ, a k = b k

end MathlibExt.Analysis.SpecificLimits.PowerSeriesCoeffEqOfAgreeOnReciprocalsWanted
