/-
# Lp→Lq bound for functions with Fourier support of finite measure

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_47.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_47 … := by sorry` into the Batteries `theorem_wanted`
`exists_const_norm_toLp_le_volume_rpow_mul_norm_toLp_of_tsupport_fourier_subset`; moved the
informal problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.BernsteinFourierSupportLpLqWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.BernsteinFourierSupportLpLqWanted

/-- **Bernstein inequality for Schwartz functions with Fourier support of finite measure.**
Fix $n \in \mathbb{N}$. For a Schwartz function $f : \mathbb{R}^n \to \mathbb{C}$ write
$\hat f(\xi) = \int_{\mathbb{R}^n} f(x) e^{-2\pi i \langle x, \xi \rangle}\,dx$ for its Fourier
transform, and write $|E|$ for the Lebesgue measure of a set $E \subseteq \mathbb{R}^n$. There
is a constant $C > 0$ such that for every Borel set $E \subseteq \mathbb{R}^n$ with
$|E| < \infty$, all $p, q \in [1, \infty]$ with $p \le q$ and $p \le 2$, and every Schwartz
function $f : \mathbb{R}^n \to \mathbb{C}$ whose Fourier transform has closed support
$\overline{\{\xi : \hat f(\xi) \ne 0\}}$ contained in $E$,
$$\|f\|_{L^q(\mathbb{R}^n)} \le C\, |E|^{1/p - 1/q}\, \|f\|_{L^p(\mathbb{R}^n)},$$
where $1/q = 0$ for $q = \infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_47.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_const_norm_toLp_le_volume_rpow_mul_norm_toLp_of_tsupport_fourier_subset
    {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Set (EuclideanSpace ℝ (Fin n))),
        MeasurableSet E →
        (MeasureTheory.volume E) < ⊤ →
        ∀ p q : ENNReal,
          1 ≤ p → p ≤ q → q ≤ ⊤ → p ≤ 2 →
            ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
              tsupport (fun ξ : EuclideanSpace ℝ (Fin n) => (𝓕 f) ξ) ⊆ E →
                ‖f.toLp q
                    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))‖ ≤
                  C *
                    Real.rpow (MeasureTheory.volume E).toReal
                      (1 / p.toReal -  (1 / q).toReal) *
                    ‖f.toLp p
                      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))‖

end MathlibExt.Analysis.Fourier.BernsteinFourierSupportLpLqWanted
