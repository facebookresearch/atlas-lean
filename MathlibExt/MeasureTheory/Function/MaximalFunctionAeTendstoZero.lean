/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Maximal functions of bounded a.e.-null sequences tend to zero a.e.

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_74.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_74 … := by sorry` into the Batteries `theorem_wanted`
`ae_tendsto_maximal_zero_of_ae_tendsto_zero_of_bounded`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.MaximalFunctionAeTendstoZeroWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Almost-everywhere convergence of interval maximal functions -/

@[expose] public section

open Set Filter MeasureTheory IsUnifLocDoublingMeasure
open scoped Topology

namespace MathlibExt.MeasureTheory.MaximalFunctionAeTendstoZeroWanted

private theorem Icc_mem_vitaliFamily_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) (hab : a < b) :
    Icc a b ∈ (vitaliFamily (volume : Measure ℝ) 1).setsAt x := by
  rw [Real.Icc_eq_closedBall]
  refine closedBall_mem_vitaliFamily_of_dist_le_mul _ ?_ (by linarith)
  rw [Real.dist_eq, one_mul, abs_le]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **Maximal functions of bounded a.e.-null sequences tend to zero a.e.** Let
$(f_n)_{n \in \mathbb{N}}$ be a sequence of functions $f_n : \mathbb{R} \to \mathbb{R}$, each
Lebesgue measurable on $[0,1]$, such that $f_n(x) \in [0,1]$ for every $n$ and every
$x \in [0,1]$, and $f_n(x) \to 0$ as $n \to \infty$ for almost every $x \in [0,1]$. For
$x \in [0,1]$ let
$$Mf_n(x) = \sup_I \frac{1}{|I|} \int_I |f_n(y)|\,dy,$$
where the supremum is taken over all closed intervals $I = [a,b]$ with $a < b$ and
$x \in I \subseteq [0,1]$, and $|I| = b - a$. Then $Mf_n(x) \to 0$ as $n \to \infty$ for almost
every $x \in [0,1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_74.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem ae_tendsto_maximal_zero_of_ae_tendsto_zero_of_bounded
    (f : ℕ → ℝ → ℝ)
    (hf_meas : ∀ n, AEMeasurable (f n) (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hf_range : ∀ n x, x ∈ Set.Icc (0 : ℝ) 1 → f n x ∈ Set.Icc (0 : ℝ) 1)
    (h_lim : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
        Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (0 : ℝ)))
    (Mf : ℕ → ℝ → ℝ)
    (hMf : ∀ n x, Mf n x = sSup {r : ℝ | ∃ a b : ℝ, x ∈ Set.Icc a b ∧
      Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 ∧ 0 < b - a ∧
        r = (b - a)⁻¹ * ∫ y in Set.Icc a b, |f n y| ∂MeasureTheory.volume}) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
      Filter.Tendsto (fun n => Mf n x) Filter.atTop (𝓝 (0 : ℝ)) := by
  let s : Set ℝ := Icc 0 1
  have hs : MeasurableSet s := measurableSet_Icc
  have hsfin : (volume : Measure ℝ) s ≠ ⊤ := isCompact_Icc.measure_lt_top.ne
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict s) := isFiniteMeasure_restrict.2 hsfin
  let g (n : ℕ) := s.indicator (fun y => |f n y|)
  have hg_nonneg (n : ℕ) (y : ℝ) : 0 ≤ g n y := by
    by_cases hy : y ∈ s <;> simp [g, hy]
  have hg_le_one (n : ℕ) (y : ℝ) : g n y ≤ 1 := by
    by_cases hy : y ∈ s
    · simpa only [g, indicator_of_mem hy, abs_of_nonneg (hf_range n y hy).1]
        using (hf_range n y hy).2
    · simp [g, hy]
  have hf_abs_bound (n : ℕ) : ∀ᵐ y ∂((volume : Measure ℝ).restrict s), ‖|f n y|‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem hs] with y hy
    simpa only [Real.norm_eq_abs, abs_abs, g, indicator_of_mem hy] using hg_le_one n y
  have hf_abs (n : ℕ) : IntegrableOn (fun y => |f n y|) s volume :=
    (integrable_const (1 : ℝ)).mono'
      (continuous_abs.measurable.comp_aemeasurable (hf_meas n)).aestronglyMeasurable
      (hf_abs_bound n)
  have hg (n : ℕ) : Integrable (g n) volume := (hf_abs n).integrable_indicator hs
  have hmass : Tendsto (fun n => ∫ y in s, |f n y| ∂volume) atTop (𝓝 0) := by
    have hpt : ∀ᵐ y ∂((volume : Measure ℝ).restrict s),
        Tendsto (fun n => |f n y|) atTop (𝓝 0) := by
      filter_upwards [h_lim] with y hy
      simpa only [abs_zero] using hy.abs
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun _ : ℝ => (1 : ℝ)) (fun n => (hf_abs n).aestronglyMeasurable)
      (integrable_const 1) hf_abs_bound hpt
  -- Differentiate the countably many envelopes of the tails of the sequence.
  let U (N : ℕ) (y : ℝ) : ℝ := ⨆ k : ℕ, g (N + k) y
  have hleU (N k : ℕ) (y : ℝ) : g (N + k) y ≤ U N y := by
    have hb : BddAbove (range (fun i : ℕ => g (N + i) y)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨i, rfl⟩
      exact hg_le_one (N + i) y
    exact le_ciSup hb k
  have hU_nonneg (N : ℕ) (y : ℝ) : 0 ≤ U N y := (hg_nonneg (N + 0) y).trans (hleU N 0 y)
  have hU (N : ℕ) : Integrable (U N) volume := by
    have hm : AEMeasurable (U N) volume :=
      AEMeasurable.iSup (fun k : ℕ => (hg (N + k)).aestronglyMeasurable.aemeasurable)
    apply ((integrableOn_const (C := (1 : ℝ)) hsfin).integrable_indicator hs).mono'
      hm.aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_of_nonneg (hU_nonneg N y)]
    apply ciSup_le
    intro k
    by_cases hy : y ∈ s
    · simpa only [indicator_of_mem hy] using hg_le_one (N + k) y
    · simp [g, hy]
  let v := vitaliFamily (volume : Measure ℝ) 1
  have hdiff : ∀ᵐ x ∂((volume : Measure ℝ).restrict s), ∀ N : ℕ,
      Tendsto (fun t => ⨍ y in t, U N y ∂volume) (v.filterAt x) (𝓝 (U N x)) := by
    apply Eventually.filter_mono (ae_mono Measure.restrict_le_self)
    exact ae_all_iff.2 (fun N : ℕ => v.ae_tendsto_average (hU N).locallyIntegrable)
  filter_upwards [ae_restrict_mem hs, h_lim, hdiff] with x hx hxlim hxdiff
  let R (n : ℕ) := {r : ℝ | ∃ a b : ℝ, x ∈ Icc a b ∧ Icc a b ⊆ s ∧ 0 < b - a ∧
      r = (b - a)⁻¹ * ∫ y in Icc a b, |f n y| ∂volume}
  have hR (n : ℕ) : Mf n x = sSup (R n) := hMf n x
  have hRnonempty (n : ℕ) : (R n).Nonempty :=
    ⟨_, ⟨0, 1, hx, Subset.rfl, by linarith, rfl⟩⟩
  have hRnonneg (n : ℕ) {r : ℝ} : r ∈ R n → 0 ≤ r := by
    rintro ⟨a, b, _, _, hab, rfl⟩
    exact mul_nonneg (inv_nonneg.mpr hab.le) (setIntegral_nonneg measurableSet_Icc
      (fun y _ => abs_nonneg (f n y)))
  have hnear (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, 0 ≤ Mf n x ∧ Mf n x ≤ ε / 2 := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hxlim).2 (ε / 4) (by linarith))
    have hUx : U N x < ε / 2 := by
      have hUle : U N x ≤ ε / 4 := by
        apply ciSup_le
        intro k
        change s.indicator (fun y => |f (N + k) y|) x ≤ ε / 4
        rw [indicator_of_mem hx, abs_of_nonneg (hf_range (N + k) x hx).1]
        exact (hN (N + k) (Nat.le_add_right N k)).le
      linarith
    obtain ⟨δ, hδ, havg⟩ := v.eventually_filterAt_iff.1
      ((tendsto_order.1 (hxdiff N)).2 (ε / 2) hUx)
    have hbig : ∀ᶠ n in atTop, (∫ y in s, |f n y| ∂volume) < δ * (ε / 2) :=
      (tendsto_order.1 hmass).2 _ (by positivity)
    filter_upwards [eventually_ge_atTop N, hbig] with n hn hbig_n
    have hupper : ∀ r ∈ R n, r ≤ ε / 2 := by
      rintro r ⟨a, b, hax, habs, hab, rfl⟩
      by_cases hshort : b - a ≤ δ
      · have hclose : Icc a b ⊆ Metric.closedBall x δ := by
          rw [Real.closedBall_eq_Icc]
          exact Icc_subset_Icc (by linarith [hax.2]) (by linarith [hax.1])
        have ha := havg (Icc a b) (Icc_mem_vitaliFamily_of_mem hax (sub_pos.mp hab)) hclose
        rw [setAverage_eq, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hab.le,
          smul_eq_mul] at ha
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        have hi : (∫ y in Icc a b, |f (N + k) y| ∂volume) ≤ ∫ y in Icc a b, U N y ∂volume := by
          apply setIntegral_mono_on ((hf_abs (N + k)).mono_set habs)
            (hU N).integrableOn measurableSet_Icc
          intro y hy
          simpa only [g, indicator_of_mem (habs hy)] using hleU N k y
        exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hab.le)).trans ha.le
      · rw [← div_eq_inv_mul, div_le_iff₀ hab]
        calc
          (∫ y in Icc a b, |f n y| ∂volume) ≤ ∫ y in s, |f n y| ∂volume :=
            setIntegral_mono_set (hf_abs n) (Eventually.of_forall fun y => abs_nonneg (f n y))
              (Eventually.of_forall habs)
          _ ≤ δ * (ε / 2) := hbig_n.le
          _ ≤ ε / 2 * (b - a) := by
            rw [mul_comm δ]
            exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hshort)) (by positivity)
    rw [hR n]
    obtain ⟨r, hr⟩ := hRnonempty n
    exact ⟨(hRnonneg n hr).trans (le_csSup ⟨ε / 2, hupper⟩ hr),
      csSup_le (hRnonempty n) hupper⟩
  refine tendsto_order.2 ⟨fun r hr => ?_, fun r hr => ?_⟩
  · exact (hnear 1 zero_lt_one).mono (fun _ h => hr.trans_le h.1)
  · exact (hnear r hr).mono (fun _ h => h.2.trans_lt (by linarith))

end MathlibExt.MeasureTheory.MaximalFunctionAeTendstoZeroWanted
