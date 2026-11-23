/-
# Lacunary series sum 2^-j z^(2^j) on the unit disc

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_09.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_09 … := by sorry` into the Batteries `theorem_wanted`
`differentiableOn_ball_continuousOn_closedBall_lacunary`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.LacunarySeriesDiscWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system; added docstrings to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.LacunarySeriesDiscWanted

/-- **A lacunary power series.** For $z \in \mathbb{C}$, let
$f(z) = \sum_{j=0}^{\infty} 2^{-j} z^{2^j}$, where $f(z)$ is taken to be $0$ when the series is
not summable. -/
noncomputable def f (z : ℂ) : ℂ :=
  ∑' j : ℕ, ((1 / (2 : ℂ)) ^ j) * z ^ (2 ^ j)

/-- **Regularity of a lacunary series on the unit disc.** Let $f$ be the lacunary series
$f(z) = \sum_{j=0}^{\infty} 2^{-j} z^{2^j}$. Then $f$ is holomorphic on the open unit disc
$\{z \in \mathbb{C} : |z| < 1\}$ and continuous on its closure, the closed unit disc
$\{z \in \mathbb{C} : |z| \le 1\}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Series expansions of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_09.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted differentiableOn_ball_continuousOn_closedBall_lacunary :
    DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      ContinuousOn f (closure (Metric.ball 0 1))

end MathlibExt.Analysis.Complex.LacunarySeriesDiscWanted
