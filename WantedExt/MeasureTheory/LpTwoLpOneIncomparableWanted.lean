/-
# L^1 and L^2 on R^d are incomparable

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_97.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_97 … := by sorry` into the Batteries `theorem_wanted`
`not_memLp_two_subset_one_and_not_memLp_one_subset_two`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LpTwoLpOneIncomparableWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.MeasureTheory.LpTwoLpOneIncomparableWanted

/-- Neither the inclusion $L^{2}(\mathbb{R}^{d}) \subset L^{1}(\mathbb{R}^{d})$ nor the inclusion
$L^{1}(\mathbb{R}^{d}) \subset L^{2}(\mathbb{R}^{d})$ is valid.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_97.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted not_memLp_two_subset_one_and_not_memLp_one_subset_two (d : ℕ) (hd : 0 < d) :
    (¬ (∀ f : (Fin d → ℝ) → ℝ,
        MeasureTheory.MemLp f 2 →
        MeasureTheory.MemLp f 1)) ∧
    (¬ (∀ f : (Fin d → ℝ) → ℝ,
        MeasureTheory.MemLp f 1 →
        MeasureTheory.MemLp f 2))

end MathlibExt.MeasureTheory.LpTwoLpOneIncomparableWanted
