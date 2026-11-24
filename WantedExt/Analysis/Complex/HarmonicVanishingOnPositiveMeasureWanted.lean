/-
# Harmonic function vanishing on a set of positive measure is zero

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_88.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_88 … := by sorry` into the Batteries `theorem_wanted`
`eq_zero_of_harmonicOnNhd_of_vanishing_on_pos_volume`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.HarmonicVanishingOnPositiveMeasureWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.HarmonicVanishingOnPositiveMeasureWanted

/-- **A harmonic function vanishing on a set of positive measure is zero.** Let
$\Omega \subseteq \mathbb{C}$ be a nonempty connected open set and let
$h : \mathbb{C} \to \mathbb{R}$ be harmonic on $\Omega$. If $h$ vanishes on some subset
$s \subseteq \Omega$ of positive (outer) Lebesgue measure, then $h(z) = 0$ for all $z \in \Omega$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Miscellaneous topics of analysis in the complex plane),
`benchmark/level2/ma_proofbench_l2_88.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted eq_zero_of_harmonicOnNhd_of_vanishing_on_pos_volume
  (Ω : Set ℂ) (h : ℂ → ℝ) (hΩ_open : IsOpen Ω) (hΩ_connected : IsConnected Ω)
  (hh_harmonic : InnerProductSpace.HarmonicOnNhd h Ω)
  (h_zero_on_pos_meas :
    ∃ s : Set ℂ, s ⊆ Ω ∧ 0 < MeasureTheory.volume s ∧ ∀ z ∈ s, h z = 0) :
  ∀ z ∈ Ω, h z = 0

end MathlibExt.Analysis.Complex.HarmonicVanishingOnPositiveMeasureWanted
