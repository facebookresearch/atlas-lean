/-
# Pointwise-convergent operators: T_n x_n → T x when x_n → x

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_68.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_68 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_apply_of_tendsto_pointwise_of_tendsto`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.PointwiseLimitOperatorsJointContinuityWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Topology Filter

namespace MathlibExt.Analysis.FunctionalAnalysis.PointwiseLimitOperatorsJointContinuityWanted

/-- Let $E$ and $F$ be two Banach spaces and let $(T_n)$ be a sequence in $\mathcal{L}(E,F)$.

Assume that for every $x\in E$, $T_nx$ converges as $n\to\infty$ to a limit denoted by $Tx$.
Show that if $x_n\to x$ in $E$, then $T_nx_n\to Tx$ in $F$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Operator theory; General theory
of linear operators), `benchmark/level1/ma_proofbench_l1_68.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_apply_of_tendsto_pointwise_of_tendsto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Tn : ℕ → E →L[ℝ] F) (T : E → F)
    (hT : ∀ x : E, Tendsto (fun n => Tn n x) atTop (𝓝 (T x))) :
    ∀ (xseq : ℕ → E) (x : E), Tendsto xseq atTop (𝓝 x) →
      Tendsto (fun n => Tn n (xseq n)) atTop (𝓝 (T x))

end MathlibExt.Analysis.FunctionalAnalysis.PointwiseLimitOperatorsJointContinuityWanted
