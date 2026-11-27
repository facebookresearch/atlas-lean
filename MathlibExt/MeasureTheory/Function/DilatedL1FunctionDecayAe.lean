/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# n^(-lambda) f(nx) -> 0 almost everywhere for f in L^1

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_37.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_37 … := by sorry` into the Batteries `theorem_wanted`
`ae_tendsto_rpow_neg_mul_comp_mul_zero`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.MeasureTheory.DilatedL1FunctionDecayAeWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Almost-everywhere decay of dilates of an integrable function -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.DilatedL1FunctionDecayAeWanted

/-- **Decay of dilates of an integrable function.** Let $f : \mathbb{R} \to \mathbb{R}$ be
Lebesgue integrable and let $\lambda > 0$. Then for almost every $x \in \mathbb{R}$,
$n^{-\lambda} f(nx) \to 0$ as $n \to \infty$ through the positive integers.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_37.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem ae_tendsto_rpow_neg_mul_comp_mul_zero
    (f : ℝ → ℝ)
    (hf : MeasureTheory.MemLp f 1 MeasureTheory.volume)
    (lam : ℝ)
    (hlam : 0 < lam) :
    ∀ᵐ x ∂MeasureTheory.volume,
      Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ (-lam) * f ((n + 1) * x))
        Filter.atTop (nhds 0) := by
  let t (n : ℕ) : ℝ := (n : ℝ) + 1
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let w (n : ℕ) : ℝ := t n ^ (-lam - 1)
  let g (n : ℕ) (x : ℝ) := t n ^ (-lam) * f (t n * x)
  let F (n : ℕ) (x : ℝ) := ‖g n x‖ₑ
  let L := ∫⁻ x : ℝ, ‖f x‖ₑ ∂volume
  have hL : L ≠ ∞ := by
    change (∫⁻ x : ℝ, ‖f x‖ₑ ∂volume) ≠ ∞
    rw [← eLpNorm_one_eq_lintegral_eNorm hf.aestronglyMeasurable]
    exact hf.eLpNorm_lt_top.ne
  have hmap (n : ℕ) : Measure.map (fun x : ℝ => t n * x) volume =
      ENNReal.ofReal (t n)⁻¹ • (volume : Measure ℝ) := by
    rw [Real.map_volume_mul_left (ht n).ne', abs_of_pos (inv_pos.mpr (ht n))]
  have hdil (n : ℕ) : Measurable (fun x : ℝ => t n * x) :=
    measurable_const.mul measurable_id
  have hquasi (n : ℕ) : QuasiMeasurePreserving (fun x : ℝ => t n * x) volume volume := by
    refine ⟨(hdil n).aemeasurable, ?_⟩
    rw [hmap n]
    exact Measure.smul_absolutelyContinuous
  have hF (n : ℕ) (x : ℝ) : F n x = ENNReal.ofReal (t n ^ (-lam)) * ‖f (t n * x)‖ₑ := by
    dsimp [F, g]
    rw [← ofReal_norm, norm_mul, Real.norm_eq_abs (t n ^ (-lam)),
      abs_of_nonneg (Real.rpow_nonneg (ht n).le _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (ht n).le _), ofReal_norm]
  have hFm (n : ℕ) : AEMeasurable (F n) volume := by
    have hg : AEMeasurable (fun x : ℝ => ‖f (t n * x)‖ₑ) volume :=
      hf.aestronglyMeasurable.eNorm.comp_quasiMeasurePreserving (hquasi n)
    exact (aemeasurable_const.mul hg).congr (.of_forall fun x => (hF n x).symm)
  -- The dilation of Lebesgue measure contributes one more inverse power of n + 1.
  have hint (n : ℕ) : (∫⁻ x : ℝ, F n x ∂volume) = ENNReal.ofReal (w n) * L := by
    have hmeas : AEMeasurable (fun x : ℝ => ‖f x‖ₑ)
        (Measure.map (fun x : ℝ => t n * x) volume) :=
      hf.aestronglyMeasurable.eNorm.mono_ac (hquasi n).absolutelyContinuous
    simp only [hF]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_map' hmeas (hdil n).aemeasurable, hmap n,
      lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (ht n).le _), ← Real.rpow_neg_one,
      ← Real.rpow_add (ht n)]
    rfl
  have hw_nonneg (n : ℕ) : 0 ≤ w n := Real.rpow_nonneg (ht n).le _
  have hw : Summable w := by
    have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-lam - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    simpa only [w, t, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have htotal : (∫⁻ x : ℝ, ∑' n : ℕ, F n x ∂volume) ≠ ∞ := by
    rw [lintegral_tsum hFm]
    simp only [hint, ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg hw_nonneg hw]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL
  -- Finite total integral gives a summable sequence of norms almost everywhere.
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hFm) htotal] with x hx
  have hlim : Tendsto (fun n => F n x) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
  change Tendsto (fun n => g n x) atTop (𝓝 0)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have htReal : Tendsto (fun n => (F n x).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hlim
  simpa only [F, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using htReal

end MathlibExt.MeasureTheory.DilatedL1FunctionDecayAeWanted
