/-
# The graph of a measurable function on R^d is a Lebesgue null set

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_38.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_38 … := by sorry` into the Batteries `theorem_wanted`
`measurableSet_and_volume_eq_zero_graph`; moved the informal problem statement docstring onto it
and placed the declarations in namespace `MathlibExt.MeasureTheory.GraphMeasurableNullWanted`;
replaced `import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory.GraphMeasurableNullWanted

/-- Let $\Gamma\subset \mathbb{R}^{d}\times\mathbb{R}$,
$\Gamma=\{(x,y)\in\mathbb{R}^{d}\times\mathbb{R}:y=f(x)\}$, and assume $f$ is measurable on
$\mathbb{R}^{d}$. Show that $\Gamma$ is a measurable subset of $\mathbb{R}^{d+1}$, and
$m(\Gamma)=0$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Measure and integration;
Classical measure theory), `benchmark/level1/ma_proofbench_l1_38.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted measurableSet_and_volume_eq_zero_graph
    {d : ℕ} (f : (Fin d → ℝ) → ℝ) (Γ : Set (Fin (d + 1) → ℝ))
    (hΓ : Γ = {z : Fin (d + 1) → ℝ | z (Fin.last d) = f (fun i : Fin d => z (Fin.castSucc i))})
    (hf : Measurable f) : MeasurableSet Γ ∧ volume Γ = 0

end MathlibExt.MeasureTheory.GraphMeasurableNullWanted
