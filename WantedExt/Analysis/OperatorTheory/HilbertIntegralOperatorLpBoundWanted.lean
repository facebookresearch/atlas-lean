/-
# Hilbert's integral operator is bounded on L^p(0,inf)

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_29.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_29 … := by sorry` into the Batteries `theorem_wanted`
`eLpNorm_hilbertIntegralOperator_le`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.HilbertIntegralOperatorLpBoundWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.OperatorTheory.HilbertIntegralOperatorLpBoundWanted

/-- **An $L^p$ bound for Hilbert's integral operator.** Let $p$ be a real number with
$p > 1$ and let $T$ be the operator on functions $g : \mathbb{R} \to \mathbb{R}$ given by
$$Tg(x) = \int_0^\infty \frac{g(y)}{x+y}\,dy \qquad (x \in \mathbb{R}).$$
Let $f : \mathbb{R} \to \mathbb{R}$ be continuous on $[0,\infty)$, compactly supported and zero
outside $[0,\infty)$, and put
$$C_p = \int_0^\infty \frac{dx}{x^{1/p}(1+x)}.$$
Then
$$\|Tf\|_{L^p([0,\infty))} \le C_p \, \|f\|_{L^p([0,\infty))},$$
where both norms are taken in $[0,\infty]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral,
integro-differential, and pseudodifferential operators),
`benchmark/level2/ma_proofbench_l2_29.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted eLpNorm_hilbertIntegralOperator_le
    (p : ℝ) (hp : 1 < p) (T : (ℝ → ℝ) → (ℝ → ℝ))
  (hT : ∀ g : ℝ → ℝ, ∀ x : ℝ, T g x = ∫ y in Set.Ici (0 : ℝ), g y / (x + y))
  (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Set.Ici (0 : ℝ)))
  (hf_cpt : HasCompactSupport f)
  (hf_support : Function.support f ⊆ Set.Ici (0 : ℝ))
  (Cp : ℝ) (hCp : Cp = ∫ x in Set.Ici (0 : ℝ), 1 / (x ^ (1 / p) * (1 + x))) :
  eLpNorm (T f) (ENNReal.ofReal p) (volume.restrict (Set.Ici (0 : ℝ))) ≤
    ENNReal.ofReal Cp * eLpNorm f (ENNReal.ofReal p) (volume.restrict (Set.Ici (0 : ℝ)))

end MathlibExt.Analysis.OperatorTheory.HilbertIntegralOperatorLpBoundWanted
