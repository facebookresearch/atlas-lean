/-
# Weighted L^6 bound with a slowly varying weight

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_67.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_67 … := by sorry` into the Batteries `theorem_wanted`
`exists_integral_pow_six_mul_weight_le`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.WeightedSixthPowerGagliardoNirenbergWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.Calculus.WeightedSixthPowerGagliardoNirenbergWanted

/-- Let $\theta:\mathbb{R}\to\mathbb{R}^{+}$ be a $C^{1}$
function such that $\|\theta'/\theta\|_{L^{\infty}(\mathbb{R})}\le 1$. Show that for all
$u\in C^{\infty}_{c}(\mathbb{R})$, there exists some absolute constant $C$ s.t.,
\[
\int_{\mathbb{R}} u^{6}\theta \le C\|u\|^{4}_{L^{2}(\mathbb{R})}\int_{\mathbb{R}}
\left(|u'|^{2}+|u|^{2}\right)\theta.
\]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_67.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_integral_pow_six_mul_weight_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (θ : ℝ → ℝ), (∀ x : ℝ, 0 < θ x) → ContDiff ℝ 1 θ →
        eLpNorm (fun x : ℝ => deriv θ x / θ x) ⊤ volume ≤ 1 →
        ∀ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
          ∫ x : ℝ, (u x) ^ (6 : ℕ) * θ x ≤
            C * (ENNReal.toReal (eLpNorm u 2 volume)) ^ (4 : ℕ) *
              ∫ x : ℝ, (|deriv u x| ^ (2 : ℕ) + |u x| ^ (2 : ℕ)) * θ x

end MathlibExt.Analysis.Calculus.WeightedSixthPowerGagliardoNirenbergWanted
