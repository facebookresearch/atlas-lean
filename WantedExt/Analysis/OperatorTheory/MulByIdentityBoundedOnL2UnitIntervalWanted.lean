/-
# Multiplication by t is a bounded operator on L²[0,1]

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_31.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_31 … := by sorry` into the Batteries `theorem_wanted`
`exists_continuousLinearMap_mul_id_L2_Icc`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.MulByIdentityBoundedOnL2UnitIntervalWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.OperatorTheory.MulByIdentityBoundedOnL2UnitIntervalWanted

/-- Consider the operator $T:L^{2}([0,1])\to L^{2}([0,1])$ defined by

\[
T(f)(t)=tf(t).
\]
Prove that $T$ is a bounded linear operator.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Operator theory; General theory
of linear operators), `benchmark/level1/ma_proofbench_l1_31.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_continuousLinearMap_mul_id_L2_Icc :
    ∃ T : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[ℝ]
        Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
        ((T f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) : ℝ → ℝ)
          =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
            fun t => t * (f : ℝ → ℝ) t

end MathlibExt.Analysis.OperatorTheory.MulByIdentityBoundedOnL2UnitIntervalWanted
