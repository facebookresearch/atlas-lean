/-
# Differentiating ∫∑f_n term by term under absolute continuity

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_50.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_50 … := by sorry` into the Batteries `theorem_wanted`
`exists_hasDerivAt_integral_tsum_ae`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.MeasureTheory.DerivIntegralSeriesAbsContWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; corrected the statement: added the source's
hypothesis that each `f n` is measurable on `Ω × (a, b)` (`h_meas`), without which the statement
is false.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Filter MeasureTheory

namespace MathlibExt.MeasureTheory.DerivIntegralSeriesAbsContWanted

/-- Let $\Omega$ be an open subset of $\mathbb{R}^d$ and $a<b$ be real numbers. For any positive
integer $n$ let $f_n(x,y)$ be a complex-valued measurable function on $\Omega\times(a,b)$. Let
$a<c<b$. Assume that for each positive integer $n$ the following three conditions are satisfied.
\begin{enumerate}
\item For each $n$ and for almost all $x\in\Omega$ the function $f_n(x,y)$ as a function of $y$ is
absolutely continuous in $y$ for $y\in(a,b)$.
\item The function $\partial f_n/\partial y$ is measurable on $\Omega\times(a,b)$ for each $n$ and
the function
\[
\sum_{n=1}^\infty \left|\frac{\partial f_n}{\partial y}(x,y)\right|
\]
is integrable on $\Omega\times(a,b)$.
\item The function $\sum_{n=1}^\infty |f_n(x,c)|$ is integrable on $\Omega$.
\end{enumerate}
Prove that the function
\[
y\mapsto \int_{x\in\Omega}\sum_{n=1}^\infty f_n(x,y)\,dx
\]
is a well-defined function for almost all $y\in(a,b)$ and that
\[
\frac{d}{dy}\int_{x\in\Omega}\sum_{n=1}^\infty f_n(x,y)\,dx
=
\sum_{n=1}^\infty \int_{x\in\Omega} \frac{\partial f_n}{\partial y}(x,y)\,dx
\]
for almost all $y\in(a,b)$.

Lean variant: the source assumes each `f n` measurable on `Ω × (a, b)`, which the original Lean
statement omitted (a non-measurable `f 0` of modulus one with `f n = 0` otherwise satisfies every
other hypothesis and breaks the conclusion); it is restored as `h_meas`.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_50.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
public theorem_wanted exists_hasDerivAt_integral_tsum_ae
    {d : ℕ} (Ω : Set (Fin d → ℝ)) (hΩ : IsOpen Ω)
    (a b c : ℝ) (hab : a < b) (hac : a < c) (hcb : c < b)
    (f : ℕ → (Fin d → ℝ) → ℝ → ℂ)
    (h_meas : ∀ n : ℕ,
      AEStronglyMeasurable (fun p : (Fin d → ℝ) × ℝ => f n p.1 p.2)
        ((volume.restrict Ω).prod (volume.restrict (Set.Ioo a b))))
    (h_ac : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict Ω),
      AbsolutelyContinuousOnInterval (fun y => f n x y) a b)
    (h_deriv_meas : ∀ n : ℕ,
      AEStronglyMeasurable (fun p : (Fin d → ℝ) × ℝ =>
        deriv (fun y => f n p.1 y) p.2)
        ((volume.restrict Ω).prod (volume.restrict (Set.Ioo a b))))
    (h_deriv_sum_finite_ae :
      ∀ᵐ p ∂((volume.restrict Ω).prod (volume.restrict (Set.Ioo a b))),
        Summable (fun n : ℕ => ‖deriv (fun y => f n p.1 y) p.2‖))
    (h_deriv_int :
      Integrable (fun p : (Fin d → ℝ) × ℝ =>
        ∑' n : ℕ, ‖deriv (fun y => f n p.1 y) p.2‖)
        ((volume.restrict Ω).prod (volume.restrict (Set.Ioo a b))))
    (h_at_c_sum_finite_ae :
      ∀ᵐ x ∂(volume.restrict Ω), Summable (fun n : ℕ => ‖f n x c‖))
    (h_at_c :
      Integrable (fun x : Fin d → ℝ => ∑' n : ℕ, ‖f n x c‖) (volume.restrict Ω)) :
    ∃ F : ℝ → ℂ,
      (∀ᵐ y ∂(volume.restrict (Set.Ioo a b)),
        Integrable (fun x : Fin d → ℝ => ∑' n : ℕ, f n x y) (volume.restrict Ω)) ∧
      (∀ᵐ y ∂(volume.restrict (Set.Ioo a b)),
        F y = ∫ x, ∑' n : ℕ, f n x y ∂(volume.restrict Ω)) ∧
      (∀ᵐ y ∂(volume.restrict (Set.Ioo a b)),
        HasDerivAt F (∑' n : ℕ, ∫ x, deriv (fun t => f n x t) y ∂(volume.restrict Ω)) y)

end MathlibExt.MeasureTheory.DerivIntegralSeriesAbsContWanted
