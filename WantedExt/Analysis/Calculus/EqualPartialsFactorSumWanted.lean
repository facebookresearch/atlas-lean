/-
# Equal partials and f(0,0)=0 give f(x,y) = g(x,y)(x+y)

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_02.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_02 … := by sorry` into the Batteries `theorem_wanted`
`exists_continuous_mul_add_of_fderiv_eq`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.EqualPartialsFactorSumWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Calculus.EqualPartialsFactorSumWanted

/-- The function $f\in C^{1}(\mathbb{R}^{2},\mathbb{R})$ satisfies $\partial_{1}f=\partial_{2}f$ and
$f(0,0)=0$. Show that there is a

$g\in C(\mathbb{R}^{2},\mathbb{R})$ such that $f(x,y)=g(x,y)(x+y)$ for $(x,y)\in\mathbb{R}^{2}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_02.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_continuous_mul_add_of_fderiv_eq {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hpar : ∀ p : ℝ × ℝ, (fderiv ℝ f p) (1, 0) = (fderiv ℝ f p) (0, 1))
    (h0 : f (0, 0) = 0) :
    ∃ g : ℝ × ℝ → ℝ, Continuous g ∧
      ∀ x y : ℝ, f (x, y) = g (x, y) * (x + y)

end MathlibExt.Analysis.Calculus.EqualPartialsFactorSumWanted
