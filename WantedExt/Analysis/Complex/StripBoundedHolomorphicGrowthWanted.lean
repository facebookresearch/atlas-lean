/-
# Growth bound for disc maps into the strip |Re w| < 1

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_86.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_86 … := by sorry` into the Batteries `theorem_wanted`
`norm_le_two_div_pi_mul_log_of_abs_re_lt_one`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.StripBoundedHolomorphicGrowthWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added docstrings to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.StripBoundedHolomorphicGrowthWanted

/-- The open unit disc. -/
abbrev D : Set ℂ := Metric.ball (0 : ℂ) 1

/-- Let $D=\{z:|z|<1\}\subset\mathbb{C}$ be the unit disk and $g:D\to\mathbb{C}$ be a holomorphic
function such that $g(0)=0$ and $|\operatorname{Re} g(z)|<1$ for any $z\in D$. Prove that for any
$z\in D$,
\[
|g(z)|\le \frac{2}{\pi}\log\frac{1+|z|}{1-|z|}.
\]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_86.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted norm_le_two_div_pi_mul_log_of_abs_re_lt_one
  (g : ℂ → ℂ)
  (hg_holo : DifferentiableOn ℂ g D)
  (hg0 : g 0 = 0)
  (hRe : ∀ z : ℂ, z ∈ D → |(Complex.re (g z))| < 1) :
  ∀ z : ℂ,
    z ∈ D →
      ‖g z‖ ≤ (2 / Real.pi) * Real.log ((1 + ‖z‖) / (1 - ‖z‖))

end MathlibExt.Analysis.Complex.StripBoundedHolomorphicGrowthWanted
