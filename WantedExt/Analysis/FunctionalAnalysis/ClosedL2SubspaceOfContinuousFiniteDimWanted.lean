/-
# Closed subspace of L^2[0,1] of continuous functions is finite-dim

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_11.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_11 … := by sorry` into the Batteries `theorem_wanted`
`finiteDimensional_of_isClosed_of_le_range_toLp`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.ClosedL2SubspaceOfContinuousFiniteDimWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ClosedL2SubspaceOfContinuousFiniteDimWanted

/-- Suppose $H$ is a closed subspace of $L^2([0, 1])$ such that $H \subset C([0, 1])$. Prove that
$H$ is finite-dimensional.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_11.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted finiteDimensional_of_isClosed_of_le_range_toLp
    (H : Submodule ℝ (MeasureTheory.Lp ℝ (2 : ENNReal)
        (MeasureTheory.volume : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))))
    (hclosed : IsClosed (H : Set (MeasureTheory.Lp ℝ (2 : ENNReal)
          (MeasureTheory.volume : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1)))))
    (hsubset : H ≤ (ContinuousMap.toLp (E := ℝ) (p := (2 : ENNReal))
        (MeasureTheory.volume : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1)) ℝ).range) :
    FiniteDimensional ℝ ↥H

end MathlibExt.Analysis.FunctionalAnalysis.ClosedL2SubspaceOfContinuousFiniteDimWanted
