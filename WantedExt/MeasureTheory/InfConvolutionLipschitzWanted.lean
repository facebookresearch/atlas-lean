/-
# The inf-convolution g_n(x) = inf_p f(p) + n·d(x,p) is n-Lipschitz

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_36.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_36 … := by sorry` into the Batteries `theorem_wanted`
`abs_toReal_g_sub_le_mul_dist`; moved the informal problem statement docstring onto it and
placed the declarations in namespace `MathlibExt.MeasureTheory.InfConvolutionLipschitzWanted`;
replaced `import Mathlib` by `public import Mathlib` under the module system; added docstrings
to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.MeasureTheory.InfConvolutionLipschitzWanted

variable {X : Type*} [MetricSpace X]

/-- The inf-convolution `g f n x = ⨅ p, f p + n * d(x, p)` of the problem, valued in `ℝ≥0∞`. -/
noncomputable def g (f : X → ENNReal) (n : ℕ) (x : X) : ENNReal :=
  sInf (Set.range fun p : X => f p + n * ENNReal.ofReal (dist x p))

/-- Suppose that $X$ is a metric space, with metric $d$, and that $f:X\to[0,\infty]$ is lower
semicontinuous, $f(p)<\infty$ for at least one $p\in X$. For $n=1,2,3,\ldots$, $x\in X$, define

\[
g_n(x)=\inf\{f(p)+nd(x,p):p\in X\}
\]
and prove that $|g_n(x)-g_n(y)|\le nd(x,y)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Nonlinear
functional analysis), `benchmark/level1/ma_proofbench_l1_36.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted abs_toReal_g_sub_le_mul_dist (f : X → ENNReal) (hf : LowerSemicontinuous f)
    (hp : ∃ p : X, f p < ⊤)
    (n : ℕ) (x y : X) :
    |(g f n x).toReal - (g f n y).toReal| ≤ n * dist x y

end MathlibExt.MeasureTheory.InfConvolutionLipschitzWanted
