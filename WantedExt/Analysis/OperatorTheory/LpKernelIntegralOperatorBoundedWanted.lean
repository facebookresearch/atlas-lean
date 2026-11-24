/-
# L^p kernel on the unit square gives a bounded operator L^q → L^p

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_87.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_87 … := by sorry` into the Batteries `theorem_wanted`
`integrable_kernel_mul_and_exists_clm_integral_operator`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.LpKernelIntegralOperatorBoundedWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory Filter

namespace MathlibExt.Analysis.OperatorTheory.LpKernelIntegralOperatorBoundedWanted

/-- **Integral operators with an $L^p$ kernel map $L^q$ to $L^p$.** Let $1 < p < \infty$ and let
$q \ge 1$ be the dual exponent, $p^{-1} + q^{-1} = 1$. Let $K : \mathbb{R}^2 \to \mathbb{R}$ lie
in $L^p((0,1)^2)$, where $L^p((0,1)^2)$, $L^p(0,1)$ and $L^q(0,1)$ are spaces of real functions
for Lebesgue measure. Then for every $f \in L^q(0,1)$ the function $y \mapsto K(x,y)f(y)$ is
integrable on $(0,1)$ for almost every $x \in (0,1)$, and there is a bounded linear operator
$A : L^q(0,1) \to L^p(0,1)$ such that for every $f \in L^q(0,1)$,
$$(Af)(x) = \int_0^1 K(x,y) f(y)\,dy \quad \text{for almost every } x \in (0,1).$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral,
integro-differential, and pseudodifferential operators),
`benchmark/level2/ma_proofbench_l2_87.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted integrable_kernel_mul_and_exists_clm_integral_operator
  (p q : ENNReal)
  [Fact (1 ≤ p)]
  [Fact (1 ≤ q)]
  (hp_ne_top : p ≠ ⊤)
  (hp_gt_one : 1 < p)
  (hq : 1 / p + 1 / q = 1)
  (K : ℝ × ℝ → ℝ)
  (hK : MemLp K p
    ((Measure.restrict volume (Set.Ioo (0 : ℝ) 1)).prod
      (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)))) :
  (∀ f : Lp ℝ q (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
      ∀ᵐ x ∂(Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
        Integrable (fun y => K (x, y) * f y) (Measure.restrict volume (Set.Ioo (0 : ℝ) 1))) ∧
    (∃ A :
      Lp ℝ q (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)) →L[ℝ]
        Lp ℝ p (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
      ∀ f : Lp ℝ q (Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
        ∀ᵐ x ∂(Measure.restrict volume (Set.Ioo (0 : ℝ) 1)),
          A f x = ∫ y, K (x, y) * f y ∂(Measure.restrict volume (Set.Ioo (0 : ℝ) 1)))

end MathlibExt.Analysis.OperatorTheory.LpKernelIntegralOperatorBoundedWanted
