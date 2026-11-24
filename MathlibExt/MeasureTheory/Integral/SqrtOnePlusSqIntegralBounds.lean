/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# √(1+A²) ≤ ∫√(1+h²) ≤ 1+A on a probability space

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_66.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_66 … := by sorry` into the Batteries `theorem_wanted`
`sqrt_one_add_sq_integral_le_and_le_one_add`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.SqrtOnePlusSqIntegralBoundsWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Two-sided square-root integral bounds on a probability space -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.MeasureTheory.SqrtOnePlusSqIntegralBoundsWanted

/-- **Two-sided bound for the integral of the square root of one plus a square.** Let $\mu$ be a
probability measure on a measurable space $\Omega$ and let $h : \Omega \to [0,\infty)$ be a
measurable function with $\int_\Omega h\,d\mu < \infty$. If $A = \int_\Omega h\,d\mu$, then
$$
\sqrt{1+A^2}\le \int_\Omega \sqrt{1+h^2}\,d\mu \le 1+A.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Measure and integration;
Classical measure theory), `benchmark/level1/ma_proofbench_l1_66.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem sqrt_one_add_sq_integral_le_and_le_one_add
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → NNReal) (hmeas : Measurable h)
    (hA_finite : (∫⁻ x, h x ∂μ) ≠ ⊤) (A : ℝ) (hA : A = (∫⁻ x, h x ∂μ).toReal) :
    Real.sqrt (1 + A ^ 2) ≤ ∫ x, Real.sqrt (1 + (h x).toReal ^ 2) ∂μ ∧
      (∫ x, Real.sqrt (1 + (h x).toReal ^ 2) ∂μ) ≤ 1 + A := by
  let u : Ω → ℝ := fun x => (h x).toReal
  let v : Ω → ℝ := fun x => Real.sqrt (1 + u x ^ 2)
  have hu_meas : Measurable u := hmeas.coe_nnreal_real
  have hu_nonneg (x : Ω) : 0 ≤ u x := NNReal.zero_le_coe
  have hu_integrable : Integrable u μ := by
    refine ⟨hu_meas.aestronglyMeasurable, hasFiniteIntegral_iff_eNorm.mpr ?_⟩
    have he (x : Ω) : ‖u x‖ₑ = (h x : ℝ≥0∞) := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hu_nonneg x)]
      exact ENNReal.ofReal_coe_nnreal
    simpa only [he] using hA_finite.lt_top
  have hu_mean : (∫ x, u x ∂μ) = A := by
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall hu_nonneg) hu_meas.aestronglyMeasurable, hA]
    simp only [u, ENNReal.ofReal_coe_nnreal]
  have hA_nonneg : 0 ≤ A := hA ▸ ENNReal.toReal_nonneg
  have hv_meas : Measurable v := (measurable_const.add (hu_meas.pow_const 2)).sqrt
  have hv_nonneg (x : Ω) : 0 ≤ v x := Real.sqrt_nonneg _
  have hv_sq (x : Ω) : v x ^ 2 = 1 + u x ^ 2 := Real.sq_sqrt (by positivity)
  have hv_upper (x : Ω) : v x ≤ 1 + u x := by
    have hpos : 0 ≤ 1 + u x := by linarith [hu_nonneg x]
    apply (sq_le_sq₀ (hv_nonneg x) hpos).mp
    rw [hv_sq]
    nlinarith [hu_nonneg x]
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
  have hu_add := hone.add hu_integrable
  have hv_integrable : Integrable v μ := hu_add.mono' hv_meas.aestronglyMeasurable <|
    .of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hv_nonneg x)]; exact hv_upper x
  have hone_mean : (∫ _ : Ω, (1 : ℝ) ∂μ) = 1 := by
    rw [integral_const, Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul]
  let s := Real.sqrt (1 + A ^ 2)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs_sq : s ^ 2 = 1 + A ^ 2 := Real.sq_sqrt (by positivity)
  -- The lower affine bound at the mean follows by squaring both nonnegative sides.
  have hv_lower (x : Ω) : (1 + A * u x) / s ≤ v x := by
    have hnonneg : 0 ≤ 1 + A * u x := by
      linarith [mul_nonneg hA_nonneg (hu_nonneg x)]
    apply (div_le_iff₀ hs_pos).mpr
    rw [mul_comm (v x) s]
    apply (sq_le_sq₀ hnonneg (mul_nonneg hs_pos.le (hv_nonneg x))).mp
    rw [mul_pow, hs_sq, hv_sq]
    nlinarith [sq_nonneg (A - u x)]
  have hAu : Integrable (fun x => A * u x) μ := hu_integrable.const_mul A
  have hw_mean : (∫ x, (1 + A * u x) / s ∂μ) = s := by
    rw [integral_div, integral_add hone hAu, integral_const_mul, hone_mean, hu_mean]
    apply (div_eq_iff hs_pos.ne').mpr
    nlinarith [hs_sq]
  change s ≤ (∫ x, v x ∂μ) ∧ (∫ x, v x ∂μ) ≤ 1 + A
  constructor
  · rw [← hw_mean]
    exact integral_mono ((hone.add hAu).div_const s) hv_integrable hv_lower
  · rw [← hone_mean, ← hu_mean, ← integral_add hone hu_integrable]
    exact integral_mono hv_integrable hu_add hv_upper

end MathlibExt.MeasureTheory.SqrtOnePlusSqIntegralBoundsWanted
