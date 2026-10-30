/-
# Monotone functions converging to a continuous limit converge uniformly

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_07.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_07 … := by sorry` into the Batteries `theorem_wanted`
`monotone_and_tendstoUniformly_of_monotone_tendsto_continuous`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.MonotonePointwiseUniformWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Filter Topology

namespace MathlibExt.Analysis.Calculus.MonotonePointwiseUniformWanted

/-- Let $(f_n)$ be a sequence of monotone functions on a compact interval $I$ which converges
pointwise to a continuous function $f$. Show that $f$ is monotone and that $(f_n)$ converges
uniformly to $f$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_07.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted monotone_and_tendstoUniformly_of_monotone_tendsto_continuous
    (a b : ℝ) (hab : a < b) (f : ℕ → (Set.Icc a b) → ℝ) (g : (Set.Icc a b) → ℝ)
    (hmono : ∀ n : ℕ, Monotone (f n))
    (hpt : ∀ x : Set.Icc a b, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hgcont : Continuous g) :
    Monotone g ∧
      TendstoUniformly (fun n x => f n x) g atTop

end MathlibExt.Analysis.Calculus.MonotonePointwiseUniformWanted
