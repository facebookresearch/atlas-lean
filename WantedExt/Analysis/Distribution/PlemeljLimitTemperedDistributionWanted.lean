/-
# 1/(x ± iε) are tempered distributions with limits as ε → 0+

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_15.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_15 … := by sorry` into the Batteries `theorem_wanted`
`exists_temperedDistribution_tendsto_inv_add_mul_I`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Distribution.PlemeljLimitTemperedDistributionWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.Distribution.PlemeljLimitTemperedDistributionWanted

noncomputable section


/-- **The pairing with $(x + i\varepsilon)^{-1}$.** For a real number $\varepsilon$ and a Schwartz
function $\phi : \mathbb{R} \to \mathbb{C}$, $u_{+,\varepsilon}(\phi)$ is the complex number
$\int_{\mathbb{R}} (x + i\varepsilon)^{-1}\phi(x)\, dx$.

The integral is the Lebesgue integral, taken to be $0$ when the integrand is not integrable;
this can happen only for $\varepsilon = 0$.
-/
def uPlusEps (ε : ℝ) (φ : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ, (((x : ℂ) + (ε : ℂ) * Complex.I)⁻¹) * φ x

/-- **The pairing with $(x - i\varepsilon)^{-1}$.** For a real number $\varepsilon$ and a Schwartz
function $\phi : \mathbb{R} \to \mathbb{C}$, $u_{-,\varepsilon}(\phi)$ is the complex number
$\int_{\mathbb{R}} (x - i\varepsilon)^{-1}\phi(x)\, dx$.

The integral is the Lebesgue integral, taken to be $0$ when the integrand is not integrable;
this can happen only for $\varepsilon = 0$.
-/
def uMinusEps (ε : ℝ) (φ : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ, (((x : ℂ) - (ε : ℂ) * Complex.I)⁻¹) * φ x

/-- **The tempered distributions $(x \pm i\varepsilon)^{-1}$ converge as $\varepsilon \to 0^+$.**
Write $S(\mathbb{R})$ for the space of complex-valued Schwartz functions on $\mathbb{R}$, and for
$\varepsilon > 0$ and $\phi \in S(\mathbb{R})$ let
$u_{\pm,\varepsilon}(\phi) = \int_{\mathbb{R}} (x \pm i\varepsilon)^{-1}\phi(x)\, dx$. Then for
every $\varepsilon > 0$ both $u_{+,\varepsilon}$ and $u_{-,\varepsilon}$ are tempered
distributions, that is, continuous $\mathbb{C}$-linear functionals on $S(\mathbb{R})$, and there
are tempered distributions $u_+$ and $u_-$ such that $u_{+,\varepsilon}(\phi) \to u_+(\phi)$ and
$u_{-,\varepsilon}(\phi) \to u_-(\phi)$ as $\varepsilon \to 0^+$ for every $\phi \in S(\mathbb{R})$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_15.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_temperedDistribution_tendsto_inv_add_mul_I :
    (∀ ε > 0,
      ∃ uPlus_eps uMinus_eps : TemperedDistribution ℝ ℂ,
        (∀ φ : SchwartzMap ℝ ℂ, uPlus_eps φ = uPlusEps ε φ) ∧
          (∀ φ : SchwartzMap ℝ ℂ, uMinus_eps φ = uMinusEps ε φ)) ∧
    (∃ uPlus uMinus : TemperedDistribution ℝ ℂ,
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun ε : ℝ => uPlusEps ε φ)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (uPlus φ))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun ε : ℝ => uMinusEps ε φ)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (uMinus φ))))

end

end MathlibExt.Analysis.Distribution.PlemeljLimitTemperedDistributionWanted
