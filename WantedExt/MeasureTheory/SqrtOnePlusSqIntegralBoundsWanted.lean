/-
# √(1+A²) ≤ ∫√(1+h²) ≤ 1+A on a probability space

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_66.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_66 … := by sorry` into the Batteries `theorem_wanted`
`sqrt_one_add_sq_integral_le_and_le_one_add`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.SqrtOnePlusSqIntegralBoundsWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory.SqrtOnePlusSqIntegralBoundsWanted

/-- Suppose $\mu(\Omega)=1$ and $h:\Omega\to[0,\infty)$ is measurable. If

\[
A=\int_\Omega h\,d\mu,
\]
prove that
\[
\sqrt{1+A^2}\le \int_\Omega \sqrt{1+h^2}\,d\mu \le 1+A.
\]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Measure and integration;
Classical measure theory), `benchmark/level1/ma_proofbench_l1_66.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted sqrt_one_add_sq_integral_le_and_le_one_add
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → NNReal) (hmeas : Measurable h)
    (hA_finite : (∫⁻ x, h x ∂μ) ≠ ⊤) (A : ℝ) (hA : A = (∫⁻ x, h x ∂μ).toReal) :
    Real.sqrt (1 + A ^ 2) ≤ ∫ x, Real.sqrt (1 + (h x).toReal ^ 2) ∂μ ∧
      (∫ x, Real.sqrt (1 + (h x).toReal ^ 2) ∂μ) ≤ 1 + A

end MathlibExt.MeasureTheory.SqrtOnePlusSqIntegralBoundsWanted
