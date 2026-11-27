/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# The L^p norm tends to the L^∞ norm as p → ∞

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_42.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_42 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_eLpNorm_atTop_eLpNorm_top_of_isFiniteMeasure`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.LpNormTendstoEssSupWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system. The move to this proved module supplies a proof
and narrows the imports, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Convergence of finite-exponent norms to the essential supremum -/

@[expose] public section

open MeasureTheory ENNReal Filter Topology
open scoped ENNReal NNReal

namespace MathlibExt.Analysis.FunctionalAnalysis.LpNormTendstoEssSupWanted

private theorem tendsto_mass_rpow_inv {m : ℝ≥0∞} (hm₀ : m ≠ 0) (hm_top : m ≠ ∞) :
    Tendsto (fun p : ℝ≥0 => m ^ (p : ℝ)⁻¹) atTop (𝓝 1) := by
  have hp : Tendsto (fun p : ℝ≥0 => (p : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp (NNReal.tendsto_coe_atTop.mpr tendsto_id)
  have hreal : Tendsto (fun p : ℝ≥0 => m.toReal ^ (p : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.rpow_zero] using
      (Real.continuousAt_const_rpow (b := 0)
        (ENNReal.toReal_ne_zero.mpr ⟨hm₀, hm_top⟩)).tendsto.comp hp
  have h := (ENNReal.continuous_ofReal.tendsto 1).comp hreal
  simp only [Function.comp_def, ENNReal.ofReal_one] at h
  apply h.congr
  intro p
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (inv_nonneg.mpr p.coe_nonneg),
    ENNReal.ofReal_toReal hm_top]

/-- **The $L^p$ norm tends to the $L^\infty$ norm.** Let $\mu$ be a finite measure on a measurable
space $\alpha$ and let $f \colon \alpha \to \mathbb{R}$ be essentially bounded,
$f \in L^\infty(\mu)$. Then $\|f\|_{L^p(\mu)} \to \|f\|_{L^\infty(\mu)}$ as the real exponent
$p$ tends to $\infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_42.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem tendsto_eLpNorm_atTop_eLpNorm_top_of_isFiniteMeasure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hmu : μ Set.univ < ∞) {f : α → ℝ} (hf : MemLp f ∞ μ) :
    Tendsto (fun p : NNReal => eLpNorm f p μ) atTop
      (𝓝 (eLpNorm f ∞ μ)) := by
  by_cases hμ₀ : μ = 0
  · simp [hμ₀]
  let S := eLpNorm f ∞ μ
  have hS : S = essSup (fun x => ‖f x‖ₑ) μ := by
    rw [show S = eLpNorm f ∞ μ from rfl, eLpNorm_exponent_top hf.aestronglyMeasurable,
      eLpNormEssSup_eq_essSup_eNorm]
  change Tendsto _ atTop (𝓝 S)
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hab, hbS⟩ := exists_between ha
    let A : Set α := {x | b ≤ ‖f x‖ₑ}
    have hA₀ : μ A ≠ 0 := by
      intro hzero
      have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ < b := by
        rw [ae_iff]
        simpa only [A, not_lt] using hzero
      exact hbS.not_ge (hS.symm ▸ essSup_le_of_ae_le b (hae.mono fun _ hx => hx.le))
    have hA_top : μ A ≠ ∞ := ((measure_mono (Set.subset_univ A)).trans_lt hmu).ne
    have hlim : Tendsto (fun p : ℝ≥0 => b * μ A ^ (p : ℝ)⁻¹) atTop (𝓝 b) := by
      simpa only [mul_one] using
        ENNReal.Tendsto.const_mul (a := b) (tendsto_mass_rpow_inv hA₀ hA_top)
          (Or.inl one_ne_zero)
    filter_upwards [hlim.eventually_const_lt hab, eventually_gt_atTop (0 : ℝ≥0)] with p hd hp
    have hpR : (0 : ℝ) < p := NNReal.coe_pos.mpr hp
    refine hd.trans_le ?_
    -- Chebyshev–Markov, followed by the positive `p`th root.
    have hmarkov : b ^ (p : ℝ) * μ A ≤ eLpNorm f p μ ^ (p : ℝ) := by
      simpa only [A, ENNReal.coe_toReal] using
        mul_meas_ge_le_pow_eLpNorm' μ ((ENNReal.coe_pos.mpr hp).ne') ENNReal.coe_ne_top (f := f) b
    convert (ENNReal.rpow_inv_le_iff hpR).mpr hmarkov using 1
    rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hpR.le), ← ENNReal.rpow_mul,
      mul_inv_cancel₀ hpR.ne', ENNReal.rpow_one]
  · intro a ha
    have hlim : Tendsto (fun p : ℝ≥0 => S * μ Set.univ ^ (p : ℝ)⁻¹) atTop (𝓝 S) := by
      simpa only [mul_one] using ENNReal.Tendsto.const_mul (a := S)
        (tendsto_mass_rpow_inv (Measure.measure_univ_eq_zero.not.mpr hμ₀) hmu.ne)
        (Or.inl one_ne_zero)
    have hbound : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ S := hS.symm ▸ ae_le_essSup
    filter_upwards [hlim.eventually_lt_const ha] with p hp
    have he := eLpNorm_le_of_ae_eNorm_bound (p := (p : ℝ≥0∞)) hf.aestronglyMeasurable hbound
    exact (by simpa only [smul_eq_mul, ENNReal.coe_toReal] using he :
      eLpNorm f p μ ≤ S * μ Set.univ ^ (p : ℝ)⁻¹).trans_lt hp

end MathlibExt.Analysis.FunctionalAnalysis.LpNormTendstoEssSupWanted
