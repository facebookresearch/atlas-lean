/-
# Continuous BV function is a difference of continuous monotone functions

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_33.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_33 … := by sorry` into the Batteries `theorem_wanted`
`exists_continuous_monotone_sub_of_boundedVariationOn`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.ContinuousBVDiffContinuousMonotoneWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.MeasureTheory.ContinuousBVDiffContinuousMonotoneWanted

/-- Suppose $F$ is of bounded variation and continuous. Prove that $F=F_1-F_2$, where both $F_1$ and
$F_2$ are monotonically non-decreasing and continuous.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_33.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_continuous_monotone_sub_of_boundedVariationOn
    {F : ℝ → ℝ} (hF_bv : BoundedVariationOn F (Set.univ : Set ℝ))
    (hF_cont : Continuous F) :
    ∃ F₁ F₂ : ℝ → ℝ, Monotone F₁ ∧ Continuous F₁ ∧ Monotone F₂ ∧ Continuous F₂ ∧ F = F₁ - F₂

end MathlibExt.MeasureTheory.ContinuousBVDiffContinuousMonotoneWanted
