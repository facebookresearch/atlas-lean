/-
# Maximal functions of bounded a.e.-null sequences tend to zero a.e.

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_74.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_74 … := by sorry` into the Batteries `theorem_wanted`
`ae_tendsto_maximal_zero_of_ae_tendsto_zero_of_bounded`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.MaximalFunctionAeTendstoZeroWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped Topology

namespace MathlibExt.MeasureTheory.MaximalFunctionAeTendstoZeroWanted

/-- Let $f_n : [0,1] \to [0,1]$ be a sequence of Lebesgue measurable functions such that $\lim_{n
\to \infty} f_n(x) = 0$ almost everywhere. Let
\[
Mf_n(x) = \sup_{x \in I \subset [0,1]} \frac{1}{|I|} \int_I |f(y)|\,dy,
\]
where the maximum is taken over closed intervals, be the Hardy--Littlewood maximal function. Show
that $\lim_{n \to \infty} Mf_n = 0$ a.e.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_74.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted ae_tendsto_maximal_zero_of_ae_tendsto_zero_of_bounded
    (f : ℕ → ℝ → ℝ)
    (hf_meas : ∀ n, AEMeasurable (f n) (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hf_range : ∀ n x, x ∈ Set.Icc (0 : ℝ) 1 → f n x ∈ Set.Icc (0 : ℝ) 1)
    (h_lim : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
        Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (0 : ℝ)))
    (Mf : ℕ → ℝ → ℝ)
    (hMf : ∀ n x, Mf n x = sSup {r : ℝ | ∃ a b : ℝ, x ∈ Set.Icc a b ∧
      Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 ∧ 0 < b - a ∧
        r = (b - a)⁻¹ * ∫ y in Set.Icc a b, |f n y| ∂MeasureTheory.volume}) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
      Filter.Tendsto (fun n => Mf n x) Filter.atTop (𝓝 (0 : ℝ))

end MathlibExt.MeasureTheory.MaximalFunctionAeTendstoZeroWanted
