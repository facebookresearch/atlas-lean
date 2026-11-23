/-
# Weighted Ladyzhenskaya inequality on ℝ² with log-Lipschitz weight

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_48.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_48 … := by sorry` into the Batteries `theorem_wanted`
`exists_const_integral_pow_four_mul_weight_le`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.WeightedLadyzhenskayaPlaneWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; wrote the regularity
hypothesis `ContDiff ℝ (⊤ : ℕ∞) u` in the equivalent scoped form `ContDiff ℝ ∞ u`
(both elaborate to `((⊤ : ℕ∞) : WithTop ℕ∞)`, ordinary smoothness; analyticity is the
distinct order `ω = (⊤ : WithTop ℕ∞)`; the weight binder is renamed `ω` to `w` because
the `ContDiff` scope reserves `ω` for the analytic order).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

open scoped ContDiff

namespace MathlibExt.Analysis.FunctionalAnalysis.WeightedLadyzhenskayaPlaneWanted

/-- **Weighted Ladyzhenskaya inequality in the plane.** There is a constant $C > 0$ such that
for every $C^1$ function $\omega : \mathbb{R}^2 \to \mathbb{R}$ with $\omega(x) > 0$ for all $x$
and $\|\nabla\omega/\omega\|_{L^\infty(\mathbb{R}^2)} \le 1$, and every smooth compactly supported
function $u : \mathbb{R}^2 \to \mathbb{R}$,
$$
\int_{\mathbb{R}^2} u^4 \omega \le C \|u\|_{L^2(\mathbb{R}^2)}^2
\int_{\mathbb{R}^2} \left(|\nabla u|^2 + |u|^2\right) \omega.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_48.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_const_integral_pow_four_mul_weight_le :
  ∃ C : ℝ, 0 < C ∧
    ∀ w : EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ x : EuclideanSpace ℝ (Fin 2), 0 < w x) →
      ContDiff ℝ 1 w →
      eLpNorm (fun x : EuclideanSpace ℝ (Fin 2) => ‖fderiv ℝ w x‖ / w x) ⊤ volume ≤ 1 →
      ∀ u : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
        ∫ x : EuclideanSpace ℝ (Fin 2), (u x) ^ (4 : ℕ) * w x ≤
          C * (ENNReal.toReal (eLpNorm u 2 volume)) ^ (2 : ℕ) *
            ∫ x : EuclideanSpace ℝ (Fin 2), (‖fderiv ℝ u x‖ ^ (2 : ℕ) + |u x| ^ (2 : ℕ)) * w x

end MathlibExt.Analysis.FunctionalAnalysis.WeightedLadyzhenskayaPlaneWanted
