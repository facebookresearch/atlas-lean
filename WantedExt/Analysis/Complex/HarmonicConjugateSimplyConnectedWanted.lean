/-
# Harmonic functions on simply connected domains are real parts

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_69.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_69 … := by sorry` into the Batteries `theorem_wanted`
`exists_differentiableOn_re_eq_of_harmonicOnNhd_of_isSimplyConnected`; moved the informal
problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnectedWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnectedWanted

/-- **Harmonic functions on simply connected domains are real parts.** Let
$\Omega \subseteq \mathbb{C}$ be a simply connected open set and let $u : \mathbb{C} \to \mathbb{R}$
be harmonic on $\Omega$. Then there is a function $f$ holomorphic on $\Omega$ with
$\operatorname{Re} f(z) = u(z)$ for all $z \in \Omega$, and $f$ is unique up to an additive
constant: if $f$ and $g$ are holomorphic on $\Omega$ with $\operatorname{Re} f(z) = u(z)$ and
$\operatorname{Re} g(z) = u(z)$ for all $z \in \Omega$, then there is $c \in \mathbb{C}$ with
$f(z) = g(z) + c$ for all $z \in \Omega$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level2/ma_proofbench_l2_69.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_differentiableOn_re_eq_of_harmonicOnNhd_of_isSimplyConnected
  (Ω : Set ℂ)
  (u : ℂ → ℝ)
  (hΩ_open : IsOpen Ω)
  (hΩ : IsSimplyConnected Ω)
  (hu : InnerProductSpace.HarmonicOnNhd u Ω) :
  (∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ ∀ z : ℂ, z ∈ Ω → Complex.re (f z) = u z) ∧
    (∀ f g : ℂ → ℂ,
      DifferentiableOn ℂ f Ω →
      DifferentiableOn ℂ g Ω →
      (∀ z : ℂ, z ∈ Ω → Complex.re (f z) = u z) →
      (∀ z : ℂ, z ∈ Ω → Complex.re (g z) = u z) →
      ∃ c : ℂ, ∀ z : ℂ, z ∈ Ω → f z = g z + c)

end MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnectedWanted
