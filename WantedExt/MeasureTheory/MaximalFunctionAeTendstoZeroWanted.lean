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

/-- **Maximal functions of bounded a.e.-null sequences tend to zero a.e.** Let
$(f_n)_{n \in \mathbb{N}}$ be a sequence of functions $f_n : \mathbb{R} \to \mathbb{R}$, each
Lebesgue measurable on $[0,1]$, such that $f_n(x) \in [0,1]$ for every $n$ and every
$x \in [0,1]$, and $f_n(x) \to 0$ as $n \to \infty$ for almost every $x \in [0,1]$. For
$x \in [0,1]$ let
$$Mf_n(x) = \sup_I \frac{1}{|I|} \int_I |f_n(y)|\,dy,$$
where the supremum is taken over all closed intervals $I = [a,b]$ with $a < b$ and
$x \in I \subseteq [0,1]$, and $|I| = b - a$. Then $Mf_n(x) \to 0$ as $n \to \infty$ for almost
every $x \in [0,1]$.

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
