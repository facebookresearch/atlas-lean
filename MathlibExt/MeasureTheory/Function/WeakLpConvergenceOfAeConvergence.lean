/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Bounded a.e.-convergent L^p sequences converge weakly (1<p<∞)

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_82.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_82 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_integral_mul_of_ae_tendsto_of_eLpNorm_bounded`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.WeakLpConvergenceOfAeConvergenceWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.UnifTight

/-! # Weak convergence of bounded almost-everywhere convergent sequences in Lebesgue Lᵖ -/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

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
theorem tendsto_integral_mul_of_ae_tendsto_of_eLpNorm_bounded
    (p q : ENNReal)
    (hp : 1 < p)
    (hp_top : p < ⊤)
    (hq : 1 / p + 1 / q = 1)
    (f : ℝ → ℝ)
    (fn : ℕ → ℝ → ℝ)
    (hfnLp : ∀ n : ℕ, MeasureTheory.MemLp (fn n) p MeasureTheory.volume)
    (hfLp : MeasureTheory.MemLp f p MeasureTheory.volume)
    (hae : ∀ᵐ x ∂MeasureTheory.volume,
      Filter.Tendsto (fun n : ℕ => fn n x) Filter.atTop (nhds (f x)))
    (hbound : ∃ M : ENNReal, M < ⊤ ∧
      ∀ n : ℕ, MeasureTheory.eLpNorm (fn n) p MeasureTheory.volume ≤ M)
    (g : ℝ → ℝ)
    (hg : MeasureTheory.MemLp g q MeasureTheory.volume) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x : ℝ, fn n x * g x)
      Filter.atTop
      (nhds (∫ x : ℝ, f x * g x)) := by
  let μ : Measure ℝ := volume
  let : p.HolderConjugate q := ENNReal.holderConjugate_iff.mpr (by simpa only [one_div] using hq)
  have hq_one : 1 ≤ q := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp_top).le
  have hq_fin : q ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp).ne
  obtain ⟨M, hM, hfn⟩ := hbound
  let F (n : ℕ) (x : ℝ) := fn n x * g x
  let G (x : ℝ) := f x * g x
  have hF (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    (hfnLp n).aestronglyMeasurable.mul hg.aestronglyMeasurable
  have hG : AEStronglyMeasurable G μ := hfLp.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have hFi (n : ℕ) : Integrable (F n) μ := (hfnLp n).integrable_mul hg
  have hGi : Integrable G μ := hfLp.integrable_mul hg
  -- Hölder bounds the restricted products by the common Lᵖ bound times the restricted Lᑫ norm.
  have hprod (n : ℕ) (s : Set ℝ) :
      eLpNorm (F n) 1 (μ.restrict s) ≤ M * eLpNorm g q (μ.restrict s) := by
    have hfns : eLpNorm (fn n) p (μ.restrict s) ≤ M :=
      (eLpNorm_restrict_le (fn n) p μ s).trans (hfn n)
    calc
      eLpNorm (F n) 1 (μ.restrict s)
          ≤ eLpNorm (fn n) p (μ.restrict s) * eLpNorm g q (μ.restrict s) := by
            simpa only [ENNReal.coe_one, one_mul] using
              (eLpNorm_le_eLpNorm_mul_eLpNorm (μ := μ.restrict s) (p := p) (q := q) (r := 1)
                (fun a b : ℝ => a * b) 1 (continuous_fst.mul continuous_snd)
                (hfnLp n).aestronglyMeasurable.restrict hg.aestronglyMeasurable.restrict
                (.of_forall fun x => by rw [nnNorm_mul, one_mul]))
      _ ≤ M * eLpNorm g q (μ.restrict s) := mul_le_mul' hfns le_rfl
  have hcut (ε : ENNReal) (hε : 0 < ε) : ∃ δ > 0, M * δ ≤ ε := by
    let C := M + 1
    have hCfin : C ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hM.ne, ENNReal.one_ne_top⟩
    have hC0 : C ≠ 0 := by simp [C]
    have hMC : M ≤ C := by
      change M ≤ M + 1
      simpa only [add_zero] using add_le_add_right (show (0 : ENNReal) ≤ 1 from bot_le) M
    refine ⟨ε / C, ENNReal.div_pos hε.ne' hCfin, ?_⟩
    calc
      M * (ε / C) ≤ C * (ε / C) := mul_le_mul' hMC le_rfl
      _ = ε := by
        rw [div_eq_mul_inv, mul_left_comm C ε, ENNReal.mul_inv_cancel hC0 hCfin, mul_one]
  have hUI : UnifIntegrable F 1 μ := by
    refine unifIntegrable_iff'.mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hscale⟩ := hcut ε hε
    obtain ⟨η, hη, hsmall⟩ := hg.eLpNorm_indicator_le hq_one hq_fin hδ
    refine ⟨η, hη, fun n s hs hμs => ?_⟩
    have hgs : eLpNorm g q (μ.restrict s) ≤ δ := by
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
      exact hsmall s hs.nullMeasurableSet hμs
    exact (hprod n s).trans ((mul_le_mul' le_rfl hgs).trans hscale)
  -- On the whole line the products must also be small outside a common finite-measure set.
  have hUT : UnifTight F 1 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hscale⟩ := hcut ε hε
    obtain ⟨s, hs, hμs, htail⟩ := hg.exists_eLpNorm_indicator_compl_lt hq_fin hδ.ne'
    refine ⟨s, hμs.ne, fun n => ?_⟩
    have hgs : eLpNorm g q (μ.restrict sᶜ) ≤ δ := by
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs.compl.nullMeasurableSet]
      exact htail.le
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs.compl.nullMeasurableSet]
    exact (hprod n sᶜ).trans ((mul_le_mul' le_rfl hgs).trans hscale)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
    filter_upwards [hae] with x hx
    exact hx.mul_const (g x)
  have hL1 : Tendsto (fun n => eLpNorm (F n - G) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_of_tendsto_ae le_rfl ENNReal.one_ne_top hF
      (memLp_one_iff_integrable.mpr hGi) hUI hUT hlim
  have hreal : Tendsto (fun n => (eLpNorm (F n - G) 1 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hL1
  change Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, G x ∂μ))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) ?_ hreal
  intro n
  rw [← integral_sub (hFi n) hGi]
  calc
    ‖∫ x, (F n - G) x ∂μ‖ ≤ ∫ x, ‖(F n - G) x‖ ∂μ := norm_integral_le_integral_norm _
    _ = (eLpNorm (F n - G) 1 μ).toReal := by
      rw [integral_norm_eq_lintegral_eNorm ((hF n).sub hG),
        eLpNorm_one_eq_lintegral_eNorm ((hF n).sub hG)]

end MathlibExt.MeasureTheory.WeakLpConvergenceOfAeConvergenceWanted
