/-
# Bounded a.e.-null sequences in L^p converge weakly to 0

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_10.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_10 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_integral_mul_of_ae_tendsto_zero_of_eLpNorm_le_one`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory Filter

namespace MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted

/-- **Lebesgue measure on $(0,1)$.** The measure on $\mathbb{R}$ obtained by restricting
Lebesgue measure to the open interval $(0, 1)$. -/
noncomputable abbrev μI01 : Measure ℝ := Measure.restrict volume (Set.Ioo (0 : ℝ) 1)

/-- **Bounded a.e.-null sequences in $L^p(0,1)$ converge weakly to zero.** Let $1 < p < \infty$
and let $q$ be the conjugate exponent, so that $1/p + 1/q = 1$. Write $L^p(0,1)$ and $L^q(0,1)$
for the Lebesgue spaces of real functions on $(0,1)$ with Lebesgue measure. Let
$(f_n)_{n \in \mathbb{N}}$ be a sequence in $L^p(0,1)$ with $\|f_n\|_{L^p} \le 1$ for every $n$
and $f_n(x) \to 0$ for almost every $x \in (0,1)$. Then for every $g \in L^q(0,1)$,
$$
\int_0^1 f_n(x)\, g(x)\, dx \to 0 \quad (n \to \infty).
$$

Since $L^q(0,1)$ is the dual of $L^p(0,1)$, this says that $(f_n)$ converges weakly to $0$ in
$L^p(0,1)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_10.lean`
at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_integral_mul_of_ae_tendsto_zero_of_eLpNorm_le_one
  (p q : ENNReal)
  (hp_ne_top : p ≠ ⊤)
  (hp_gt_one : 1 < p)
  (hq : 1 / p + 1 / q = 1)
  (f : ℕ → Lp ℝ p μI01)
  (h_bound : ∀ n, eLpNorm (f n) p μI01 ≤ 1)
  (h_ae : ∀ᵐ x ∂μI01, Tendsto (fun n => f n x) atTop (nhds 0)) :
  ∀ g : Lp ℝ q μI01, Tendsto (fun n => ∫ x, (f n x) * g x ∂μI01) atTop (nhds 0)

end MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted
