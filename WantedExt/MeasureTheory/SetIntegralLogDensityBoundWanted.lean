/-
# Integral of log of a probability density over a set

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_82.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_82 … := by sorry` into the Batteries `theorem_wanted`
`setIntegral_log_le_measure_mul_log_inv_measure`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.SetIntegralLogDensityBoundWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added the hypothesis that `log f` is
integrable on `E` and stated the inequality directly (the source statement concluded with the
disjunction `(IntegrableOn … ∧ inequality) ∨ ¬IntegrableOn …`, which asserts nothing in the
nonintegrable case, where the integral is `-∞`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory.SetIntegralLogDensityBoundWanted

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Suppose $\mu$ is a positive measure on $X$ and $f:X\to(0,\infty)$ satisfies $\int_X f\,d\mu=1$.
Prove, for every $E\subset X$ with $0<\mu(E)<\infty$ such that $\log f$ is integrable on $E$,
that

\[
\int_E (\log f)\,d\mu \le \mu(E)\log\frac{1}{\mu(E)}
\]

The integrability of $\log f$ on $E$ is assumed so that the statement is real-valued: the
positive part of $\log f$ is integrable on $E$ (since $(\log f)^{+}\le f$), so if $\log f$
is not integrable on $E$ then $\int_E(\log f)\,d\mu=-\infty$ and the inequality holds in
$\mathbb{R}\cup\{-\infty\}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Measure and integration;
Classical measure theory), `benchmark/level1/ma_proofbench_l1_82.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted setIntegral_log_le_measure_mul_log_inv_measure (f : X → ℝ)
    (hf_pos : ∀ x, 0 < f x)
    (hf_int : Integrable f μ)
    (hf_one : (∫ x, f x ∂μ) = 1)
    (E : Set X) (hE_meas : MeasurableSet E)
    (hE_pos : 0 < μ E)
    (hE_fin : μ E < ⊤)
    (hf_log_int : IntegrableOn (fun x => Real.log (f x)) E μ) :
    (∫ x in E, Real.log (f x) ∂μ) ≤ (μ E).toReal * Real.log (1 / (μ E).toReal)

end MathlibExt.MeasureTheory.SetIntegralLogDensityBoundWanted
