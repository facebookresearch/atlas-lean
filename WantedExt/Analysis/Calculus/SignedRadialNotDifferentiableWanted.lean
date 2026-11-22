/-
# Signed radial function is not differentiable at the origin

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_06.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_06 … := by sorry` into the Batteries `theorem_wanted`
`not_differentiableAt_signed_norm_zero`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.SignedRadialNotDifferentiableWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Calculus.SignedRadialNotDifferentiableWanted

/-- Suppose $f:\mathbb{R}^{2}\to\mathbb{R}$ is defined by

\[
f(x,y):=
\begin{cases}
\sqrt{x^{2}+y^{2}}, & y>0,\\
x, & y=0,\\
-\sqrt{x^{2}+y^{2}}, & y<0.
\end{cases}
\]
Show $f$ is not differentiable at $(0,0)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_06.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted not_differentiableAt_signed_norm_zero
    {f : ℝ × ℝ → ℝ} (hpos : ∀ x y : ℝ, y > 0 → f (x, y) = Real.sqrt (x ^ 2 + y ^ 2))
    (hzero : ∀ x : ℝ, f (x, 0) = x)
    (hneg : ∀ x y : ℝ, y < 0 → f (x, y) = -Real.sqrt (x ^ 2 + y ^ 2)) :
    ¬ DifferentiableAt ℝ f (0, 0)

end MathlibExt.Analysis.Calculus.SignedRadialNotDifferentiableWanted
