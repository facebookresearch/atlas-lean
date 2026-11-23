/-
# Weak L^p limits of nonnegative functions are nonnegative

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_16.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_16 … := by sorry` into the Batteries `theorem_wanted`
`ae_nonneg_of_weak_tendsto_of_ae_nonneg`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.WeakLimitOfNonnegLpNonnegWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.FunctionalAnalysis.WeakLimitOfNonnegLpNonnegWanted

noncomputable section

/-- **Weak $L^p$ limits of nonnegative functions are nonnegative.** Let $1 < p < \infty$
and write $L^p([0,1])$ for the Lebesgue space of real functions on $[0,1]$ with Lebesgue measure.
Let $(f_n)_{n \in \mathbb{N}}$ be a sequence in $L^p([0,1])$ such that for each $n$,
$f_n(x) \ge 0$ for almost every $x \in [0,1]$, and let $f \in L^p([0,1])$. If $f_n$ converges
weakly to $f$, that is, $\ell(f_n) \to \ell(f)$ for every continuous linear functional
$\ell : L^p([0,1]) \to \mathbb{R}$, then $f(x) \ge 0$ for almost every $x \in [0,1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_16.lean`
at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted ae_nonneg_of_weak_tendsto_of_ae_nonneg
    (p : ENNReal)
    [Fact (1 ≤ p)]
    (hp : 1 < p ∧ p < ⊤)
    (fn : ℕ → MeasureTheory.Lp ℝ p (Measure.restrict volume (Set.Icc (0 : ℝ) 1)))
    (f : MeasureTheory.Lp ℝ p (Measure.restrict volume (Set.Icc (0 : ℝ) 1)))
    (h_nonneg : ∀ n : ℕ, ∀ᵐ x ∂(Measure.restrict volume (Set.Icc (0 : ℝ) 1)), 0 ≤ fn n x)
    (hweak : ∀ l : (MeasureTheory.Lp ℝ p (Measure.restrict volume (Set.Icc (0 : ℝ) 1))) →L[ℝ] ℝ,
      Filter.Tendsto (fun n : ℕ => l (fn n)) Filter.atTop (nhds (l f))) :
    ∀ᵐ x ∂(Measure.restrict volume (Set.Icc (0 : ℝ) 1)), 0 ≤ f x

end

end MathlibExt.Analysis.FunctionalAnalysis.WeakLimitOfNonnegLpNonnegWanted
