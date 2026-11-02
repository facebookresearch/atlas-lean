/-
# The Laplace transform is bounded on L^p(0,inf) iff p = 2

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_31.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_31 … := by sorry` into the Batteries `theorem_wanted`
`laplaceTransform_bounded_on_Lp_iff_eq_two`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.LaplaceTransformLpBoundedIffTwoWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.OperatorTheory.LaplaceTransformLpBoundedIffTwoWanted

/-- **The Laplace transform is bounded on $L^p([0,\infty))$ exactly when $p = 2$.** For a real
function $f$ on $\mathbb{R}$ let
$$Lf(s) = \int_0^\infty e^{-xs} f(x)\,dx \qquad (s \in \mathbb{R}).$$
Let $p \in [1,\infty]$. Then $p = 2$ if and only if there is a constant $C$ with $0 < C < \infty$
such that every real function $f \in L^p([0,\infty))$ satisfies $Lf \in L^p([0,\infty))$ and
$\|Lf\|_{L^p([0,\infty))} \le C\,\|f\|_{L^p([0,\infty))}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral,
integro-differential, and pseudodifferential operators),
`benchmark/level2/ma_proofbench_l2_31.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted laplaceTransform_bounded_on_Lp_iff_eq_two (p : ENNReal) (hp : 1 ≤ p) :
  (∃ C : ENNReal, 0 < C ∧ C < ⊤ ∧ ∀ f : ℝ → ℝ,
  MemLp f p (volume.restrict (Set.Ici (0 : ℝ))) →
  MemLp (fun s : ℝ => ∫ x in Set.Ici (0 : ℝ), Real.exp (-x * s) * f x) p
    (volume.restrict (Set.Ici (0 : ℝ))) ∧
  eLpNorm (fun s : ℝ => ∫ x in Set.Ici (0 : ℝ), Real.exp (-x * s) * f x) p
    (volume.restrict (Set.Ici (0 : ℝ))) ≤
  C * eLpNorm f p (volume.restrict (Set.Ici (0 : ℝ)))) ↔
  p = 2

end MathlibExt.Analysis.OperatorTheory.LaplaceTransformLpBoundedIffTwoWanted
