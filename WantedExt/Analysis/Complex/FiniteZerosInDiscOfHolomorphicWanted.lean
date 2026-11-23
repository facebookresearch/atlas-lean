/-
# A holomorphic function not identically zero has finitely many zeros in a disc

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_26.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_26 … := by sorry` into the Batteries `theorem_wanted`
`finite_zeros_in_ball_of_not_identically_zero`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.FiniteZerosInDiscOfHolomorphicWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.FiniteZerosInDiscOfHolomorphicWanted

/-- **A holomorphic function not identically zero has finitely many zeros in a disc.** Let
$P \in \mathbb{C}$ and $r > 0$, write $D(P,r)$ for the open disc and $\overline{D}(P,r)$ for the
closed disc of center $P$ and radius $r$, and let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic
on some open set containing $\overline{D}(P,r)$. If $f$ does not vanish identically on $D(P,r)$,
then $f$ has only finitely many zeros in $D(P,r)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_26.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted finite_zeros_in_ball_of_not_identically_zero
    (f : ℂ → ℂ) (P : ℂ) (r : ℝ) (hr : 0 < r)
    (hhol : ∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall P r ⊆ U ∧ DifferentiableOn ℂ f U)
    (hnot : ¬ ∀ z ∈ Metric.ball P r, f z = 0) :
    (Set.Finite {z : ℂ | z ∈ Metric.ball P r ∧ f z = 0})

end MathlibExt.Analysis.Complex.FiniteZerosInDiscOfHolomorphicWanted
