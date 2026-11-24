/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Integral of log of a probability density over a set

The following OpenBMB notice applies to the adapted statement and its documentation.

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
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_82 … := by sorry` into the Batteries `theorem_wanted`
`setIntegral_log_le_measure_mul_log_inv_measure`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.SetIntegralLogDensityBoundWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added the hypothesis that `log f` is
integrable on `E` and stated the inequality directly (the source statement concluded with the
disjunction `(IntegrableOn … ∧ inequality) ∨ ¬IntegrableOn …`, which asserts nothing in the
nonintegrable case, where the integral is `-∞`). This move proves the ATLAS statement and narrows
the imports to the modules used.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-! # A set-integral bound for the logarithm of a probability density -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.MeasureTheory.SetIntegralLogDensityBoundWanted

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- **Upper bound for the integral of the logarithm of a probability density over a set.** Let
$\mu$ be a measure on a measurable space $X$ and let $f : X \to \mathbb{R}$ be integrable with
respect to $\mu$, with $f(x) > 0$ for every $x \in X$ and $\int_X f\,d\mu = 1$. Then for every
measurable set $E \subseteq X$ with $0 < \mu(E) < \infty$ such that $\log f$ is integrable on $E$,
$$
\int_E \log f\,d\mu \le \mu(E)\log\frac{1}{\mu(E)}.
$$

The integrability of $\log f$ on $E$ is assumed so that the statement is real-valued: the
positive part of $\log f$ is integrable on $E$ (since $(\log f)^{+}\le f$), so if $\log f$
is not integrable on $E$ then $\int_E(\log f)\,d\mu=-\infty$ and the inequality holds in
$\mathbb{R}\cup\{-\infty\}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Measure and integration;
Classical measure theory), `benchmark/level1/ma_proofbench_l1_82.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem setIntegral_log_le_measure_mul_log_inv_measure (f : X → ℝ)
    (hf_pos : ∀ x, 0 < f x)
    (hf_int : Integrable f μ)
    (hf_one : (∫ x, f x ∂μ) = 1)
    (E : Set X) (hE_meas : MeasurableSet E)
    (hE_pos : 0 < μ E)
    (hE_fin : μ E < ⊤)
    (hf_log_int : IntegrableOn (fun x => Real.log (f x)) E μ) :
    (∫ x in E, Real.log (f x) ∂μ) ≤ (μ E).toReal * Real.log (1 / (μ E).toReal) := by
  let m := (μ E).toReal
  let ν := μ.restrict E
  have hm : 0 < m := ENNReal.toReal_pos hE_pos.ne' hE_fin.ne
  have hν : ν Set.univ = μ E := Measure.restrict_apply_univ E
  let : IsFiniteMeasure ν := ⟨by rw [hν]; exact hE_fin⟩
  have hf_mass : (∫ x, f x ∂ν) ≤ 1 := by
    change (∫ x in E, f x ∂μ) ≤ 1
    rw [← hf_one, ← integral_add_compl hE_meas hf_int]
    exact le_add_of_nonneg_right (integral_nonneg fun x => (hf_pos x).le)
  have hc : Integrable (fun _ : X => Real.log (1 / m)) ν := integrable_const _
  have hf_scaled : Integrable (fun x => m * f x) ν := hf_int.restrict.const_mul m
  have hdiff : Integrable (fun x => m * f x - 1) ν := hf_scaled.sub (integrable_const 1)
  -- Apply the tangent-line bound for log to the density scaled by the measure of E.
  have hle (x : X) : Real.log (f x) ≤ Real.log (1 / m) + (m * f x - 1) := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hm (hf_pos x))
    rw [Real.log_mul hm.ne' (hf_pos x).ne'] at h
    rw [Real.log_div one_ne_zero hm.ne', Real.log_one, zero_sub]
    linarith
  change (∫ x, Real.log (f x) ∂ν) ≤ m * Real.log (1 / m)
  calc
    _ ≤ ∫ x, (Real.log (1 / m) + (m * f x - 1)) ∂ν :=
      integral_mono hf_log_int (hc.add hdiff) hle
    _ = m * Real.log (1 / m) + (m * (∫ x, f x ∂ν) - m) := by
      rw [integral_add hc hdiff, integral_sub hf_scaled (integrable_const 1), integral_const_mul]
      simp only [integral_const, Measure.real_def, hν, smul_eq_mul, mul_one, m]
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hf_mass hm.le]

end MathlibExt.MeasureTheory.SetIntegralLogDensityBoundWanted
