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

/-- **Differentiating an integral of a series term by term.** Let $d \in \mathbb{N}$, let $\Omega$
be an open subset of $\mathbb{R}^d$, let $a < c < b$ be real numbers, and for each
$n \in \mathbb{N}$ let $f_n : \mathbb{R}^d \times \mathbb{R} \to \mathbb{C}$ be almost everywhere
measurable on $\Omega \times (a, b)$ with respect to Lebesgue measure. Write
$\partial_y f_n(x, y)$ for the derivative of $t \mapsto f_n(x, t)$ at $y$, taken to be $0$ where
this derivative does not exist, and give every series that does not converge absolutely the
sum $0$. Assume that:
(1) for each $n$ and almost every $x \in \Omega$, the function $y \mapsto f_n(x, y)$ is
absolutely continuous on $[a, b]$;
(2) each $\partial_y f_n$ is almost everywhere measurable on $\Omega \times (a, b)$, the series
$\sum_n |\partial_y f_n(x, y)|$ converges for almost every $(x, y) \in \Omega \times (a, b)$,
and its sum is integrable on $\Omega \times (a, b)$;
(3) the series $\sum_n |f_n(x, c)|$ converges for almost every $x \in \Omega$, and its sum is
integrable on $\Omega$.
Then there is a function $F : \mathbb{R} \to \mathbb{C}$ such that for almost every
$y \in (a, b)$ the function $x \mapsto \sum_n f_n(x, y)$ is integrable on $\Omega$,
$F(y) = \int_\Omega \sum_n f_n(x, y)\, dx$, and $F$ is differentiable at $y$ with
$$
F'(y) = \sum_n \int_\Omega \partial_y f_n(x, y)\, dx.
$$

The joint measurability of each $f_n$ is a hypothesis of the source that the first formalization
dropped. It is needed: for $d \ge 1$ and nonempty bounded $\Omega$, a non-measurable $f_0$ of
modulus one that does not depend on $y$, with $f_n = 0$ for $n \ge 1$, satisfies the other
hypotheses but not the conclusion.

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
