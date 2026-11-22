/-
# Continuous nonzero solutions of f(x)f(y) = f(x+y) are exponentials

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_32.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_32 … := by sorry` into the Batteries `theorem_wanted`
`exists_eq_exp_mul_of_map_add_eq_mul`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.SpecialFunctions.ContinuousMultiplicativeFunctionalEqExpWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.SpecialFunctions.ContinuousMultiplicativeFunctionalEqExpWanted

/-- Suppose $f(x)f(y)=f(x+y)$ for all real $x$ and $y$. Assuming that $f$ is continuous and not
zero, prove that

 \[
 f(x)=e^{cx},
 \]
 where $c$ is a constant.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_32.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_eq_exp_mul_of_map_add_eq_mul
    {f : ℝ → ℝ}
    (hadd : ∀ x y : ℝ, f x * f y = f (x + y))
    (hcont : Continuous f)
    (hnz : f ≠ 0) :
    ∃ c : ℝ, ∀ x : ℝ, f x = Real.exp (c * x)

end MathlibExt.Analysis.SpecialFunctions.ContinuousMultiplicativeFunctionalEqExpWanted
