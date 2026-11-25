/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# L^p function with finite L^q mass on finite-measure sets is in L^q

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_24.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_24 … := by sorry` into the Batteries `theorem_wanted`
`memLp_of_memLp_of_lintegral_rpow_lt_top_of_measure_lt_top`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.MemLpOfLqIntegrableOnFiniteMeasureSetsWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system. The move to this proved module
supplies a proof and narrows the imports, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-! # Finite local higher-power integrals and global `MemLp` -/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal

namespace MathlibExt.MeasureTheory.MemLpOfLqIntegrableOnFiniteMeasureSetsWanted

/-- **An $L^p$ function with finite $L^q$ mass on finite-measure sets is in $L^q$.** Let
$1 \le p < q < \infty$ and let $f : \mathbb{R} \to \mathbb{R}$ belong to $L^p(\mathbb{R})$. If
$\int_A |f|^q < \infty$ for every Borel set $A \subseteq \mathbb{R}$ of finite Lebesgue measure,
then $f \in L^q(\mathbb{R})$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_24.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem memLp_of_memLp_of_lintegral_rpow_lt_top_of_measure_lt_top
    {p q : ENNReal}
    (hp : 1 ≤ p) (hpq : p < q) (hq : q < ⊤)
    (f : ℝ → ℝ)
    (hfLp : MeasureTheory.MemLp f p MeasureTheory.volume)
    (hA : ∀ A : Set ℝ, MeasurableSet A → MeasureTheory.volume A < ⊤ →
      (∫⁻ x in A, (ENNReal.ofReal |f x|) ^ q.toReal ∂MeasureTheory.volume) < ⊤) :
    MeasureTheory.MemLp f q MeasureTheory.volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp_top : p ≠ ∞ := (hpq.trans hq).ne
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (hp.trans hpq.le)).ne'
  let g := hfLp.aestronglyMeasurable.aemeasurable.mk f
  have hg : Measurable g := hfLp.aestronglyMeasurable.aemeasurable.measurable_mk
  have hfg : f =ᵐ[volume] g := hfLp.aestronglyMeasurable.aemeasurable.ae_eq_mk
  have hgLp : MemLp g p volume := (memLp_congr_ae hfg).mp hfLp
  -- Use a Borel superlevel set, even when `f` itself is only a.e. measurable.
  let A : Set ℝ := {x | 1 ≤ ‖g x‖ₑ}
  have hAm : MeasurableSet A := measurableSet_le measurable_const hg.eNorm
  have hAv : volume A < ∞ := by
    simpa only [ENNReal.coe_one] using hgLp.meas_ge_lt_top_eNorm hp0 hp_top
      (ε := 1) one_ne_zero
  have hlarge : (∫⁻ x in A, ‖f x‖ₑ ^ q.toReal ∂volume) < ∞ := by
    simpa only [← Real.norm_eq_abs, ofReal_norm] using hA A hAm hAv
  have hsmall : (∫⁻ x in Aᶜ, ‖f x‖ₑ ^ q.toReal ∂volume) < ∞ := by
    calc
      (∫⁻ x in Aᶜ, ‖f x‖ₑ ^ q.toReal ∂volume) ≤
          ∫⁻ x in Aᶜ, ‖f x‖ₑ ^ p.toReal ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hAm.compl, ae_restrict_of_ae hfg] with x hx heq
        have hx' : ‖g x‖ₑ < 1 := lt_of_not_ge hx
        rw [heq]
        exact ENNReal.rpow_le_rpow_of_exponent_ge hx'.le (ENNReal.toReal_mono hq.ne hpq.le)
      _ ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume := setLIntegral_le_lintegral _ _
      _ < ∞ := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp_top hfLp.eLpNorm_lt_top
  apply (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
    hq0 hq.ne hfLp.aestronglyMeasurable).mpr
  rw [← lintegral_add_compl _ hAm]
  exact ENNReal.add_lt_top.mpr ⟨hlarge, hsmall⟩

end MathlibExt.MeasureTheory.MemLpOfLqIntegrableOnFiniteMeasureSetsWanted
