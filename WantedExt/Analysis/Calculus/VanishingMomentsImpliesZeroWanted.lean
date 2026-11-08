/-
# A continuous function with all vanishing moments on [0,1] is zero

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_51.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_51 … := by sorry` into the Batteries `theorem_wanted`
`eqOn_zero_of_integral_mul_pow_eq_zero`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.VanishingMomentsImpliesZeroWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Calculus.VanishingMomentsImpliesZeroWanted

/-- If $f$ is continuous on $[0,1]$ and if

\[
\int_{0}^{1} f(x)x^{n}\,dx=0\qquad (n=0,1,2,\dots),
\]
prove that $f(x)=0$ on $[0,1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_51.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted eqOn_zero_of_integral_mul_pow_eq_zero
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (h : ∀ n : ℕ, (∫ x in 0..1, f x * x ^ n) = 0) :
    Set.EqOn f 0 (Set.Icc 0 1)

end MathlibExt.Analysis.Calculus.VanishingMomentsImpliesZeroWanted
