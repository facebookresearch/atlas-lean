/-
# Weak third derivative zero implies a quadratic polynomial

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_66.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_66 … := by sorry` into the Batteries `theorem_wanted`
`ae_eq_quadratic_of_integral_mul_iteratedDeriv_three_eq_zero`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Distribution.WeakThirdDerivativeZeroQuadraticWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Distribution.WeakThirdDerivativeZeroQuadraticWanted

/-- Let $f\in L^{1}(0,1)$ be such that $\int_{0}^{1} f(x)g^{(3)}(x)\,dx=0$ for all $g\in
C_{c}^{\infty}(0,1)$, where $g^{(3)}$ is the third derivative of $g$. Show that $f$ is (almost
everywhere) a polynomial of degree at most $2$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_66.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted ae_eq_quadratic_of_integral_mul_iteratedDeriv_three_eq_zero
  (f : ℝ → ℝ)
  (hf : MeasureTheory.MemLp f 1 (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)))
  (hweak : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
    (∃ a b : ℝ, Function.support g ⊆ Set.Icc a b ∧
      Set.Icc a b ⊆ Set.Ioo (0 : ℝ) 1) →
      ∫ x in Set.Icc 0 1, f x * deriv (deriv (deriv g)) x = 0) :
  ∃ a b c : ℝ, ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)),
    f x = a + b * x + c * x ^ 2

end MathlibExt.Analysis.Distribution.WeakThirdDerivativeZeroQuadraticWanted
