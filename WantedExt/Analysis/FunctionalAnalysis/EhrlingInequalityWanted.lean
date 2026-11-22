/-
# Ehrling's lemma for a compact and a continuous embedding

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_36.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_36 … := by sorry` into the Batteries `theorem_wanted`
`ehrling_inequality`; moved the informal problem statement docstring onto it and placed the
declarations in namespace `MathlibExt.Analysis.FunctionalAnalysis.EhrlingInequalityWanted`;
replaced `import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.EhrlingInequalityWanted

/-- Let $(X,\|\cdot\|_X)$, $(Y,\|\cdot\|_Y)$, $(Z,\|\cdot\|_Z)$ be Banach spaces. Suppose $X\subset
Y$ is compact and $Y\subset Z$ is continuous. Prove that for every $\varepsilon>0$, there exists
$C_\varepsilon>0$ such that
 \[
 \|u\|_Y \le \varepsilon \|u\|_X + C_\varepsilon \|u\|_Z \qquad \forall\, u\in X.
 \]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_36.lean`
at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted ehrling_inequality
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (iXY : X →L[ℝ] Y) (iYZ : Y →L[ℝ] Z)
    (hXY_compact : IsCompactOperator (iXY : X → Y))
    (hXY_inj : Function.Injective iXY)
    (hYZ_inj : Function.Injective iYZ) :
    ∀ ε > 0, ∃ Cε > 0, ∀ u : X,
      ‖iXY u‖ ≤ ε * ‖u‖ + Cε * ‖iYZ (iXY u)‖

end MathlibExt.Analysis.FunctionalAnalysis.EhrlingInequalityWanted
