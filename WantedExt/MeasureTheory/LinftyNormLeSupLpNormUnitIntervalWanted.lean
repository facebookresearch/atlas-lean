/-
# Uniform Lp bounds for all p ≥ 1 give the same L∞ bound on [0,1]

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_52.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_52 … := by sorry` into the Batteries `theorem_wanted`
`eLpNorm_top_le_of_forall_one_le_eLpNorm_le`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LinftyNormLeSupLpNormUnitIntervalWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory.LinftyNormLeSupLpNormUnitIntervalWanted

/-- **Uniform $L^p$ bounds on $[0,1]$ give the same $L^\infty$ bound.** Let $M$ be a real number,
write $M^+ = \max(M, 0)$, and let $f_0, f_1, f_2, \dots : \mathbb{R} \to \mathbb{R}$ be functions
that are almost everywhere strongly measurable with respect to Lebesgue measure restricted to
$[0,1]$. If $\|f_n\|_{L^p[0,1]} \le M^+$ for every $n$ and every real $p \ge 1$, then
$\|f_n\|_{L^\infty[0,1]} \le M^+$ for every $n$. All norms are taken with respect to Lebesgue
measure restricted to $[0,1]$ and may be infinite.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_52.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted eLpNorm_top_le_of_forall_one_le_eLpNorm_le
    (f : ℕ → ℝ → ℝ) (M : ℝ)
    (hf : ∀ n : ℕ, AEStronglyMeasurable (f n) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hM : ∀ n : ℕ, ∀ p : ℝ, 1 ≤ p →
      eLpNorm (f n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ ENNReal.ofReal M) :
    ∀ n : ℕ, eLpNorm (f n) ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ ENNReal.ofReal M

end MathlibExt.MeasureTheory.LinftyNormLeSupLpNormUnitIntervalWanted
