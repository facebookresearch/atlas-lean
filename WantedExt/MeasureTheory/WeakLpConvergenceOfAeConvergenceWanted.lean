/-
# Bounded a.e.-convergent L^p sequences converge weakly (1<p<∞)

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_82.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_82 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_integral_mul_of_ae_tendsto_of_eLpNorm_bounded`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.WeakLpConvergenceOfAeConvergenceWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.MeasureTheory.WeakLpConvergenceOfAeConvergenceWanted

/-- **Bounded almost everywhere convergent sequences in $L^p$, $1 < p < \infty$, converge
weakly.** Let $1 < p < \infty$ and let $q$ be the conjugate exponent, $1/p + 1/q = 1$. Let $f$
and $f_0, f_1, f_2, \dots$ be real-valued functions in $L^p(\mathbb{R})$ such that $f_n \to f$
almost everywhere and $\sup_n \|f_n\|_{L^p} < \infty$. Then $f_n$ converges weakly to $f$: for
every $g \in L^q(\mathbb{R})$,
$$
\lim_{n\to\infty}\int_{\mathbb{R}} f_n g\,dx=\int_{\mathbb{R}} f g\,dx.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_82.lean`
at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_integral_mul_of_ae_tendsto_of_eLpNorm_bounded
  (p q : ENNReal)
  (hp : 1 < p)
  (hp_top : p < ⊤)
  (hq : 1 / p + 1 / q = 1)
  (f : ℝ → ℝ)
  (fn : ℕ → ℝ → ℝ)
  (hfnLp : ∀ n : ℕ, MeasureTheory.MemLp (fn n) p MeasureTheory.volume)
  (hfLp : MeasureTheory.MemLp f p MeasureTheory.volume)
  (hae : ∀ᵐ x ∂MeasureTheory.volume, Filter.Tendsto (fun n : ℕ => fn n x) Filter.atTop (nhds (f x)))
  (hbound : ∃ M : ENNReal, M < ⊤ ∧ ∀ n : ℕ, MeasureTheory.eLpNorm (fn n) p MeasureTheory.volume ≤ M)
  (g : ℝ → ℝ)
  (hg : MeasureTheory.MemLp g q MeasureTheory.volume) :
  Filter.Tendsto
    (fun n : ℕ => ∫ x : ℝ, fn n x * g x)
    Filter.atTop
    (nhds (∫ x : ℝ, f x * g x))

end MathlibExt.MeasureTheory.WeakLpConvergenceOfAeConvergenceWanted
