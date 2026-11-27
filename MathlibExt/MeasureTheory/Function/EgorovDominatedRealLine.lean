/-
# Egorov on ℝ for an integrably dominated sequence

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_43.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_43 … := by sorry` into the Batteries `theorem_wanted`
`exists_measure_lt_tendstoUniformlyOn_compl_of_ae_tendsto_of_abs_le`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.EgorovDominatedRealLineWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system. The move to this proved module supplies the proof and
narrows the imports, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Function.Egorov
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Egorov's theorem under integrable domination on the real line -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.EgorovDominatedRealLineWanted

/-- **Egorov's theorem on the real line under integrable domination.** Let
$f : \mathbb{R} \to \mathbb{R}$ be any function and let $f_n : \mathbb{R} \to \mathbb{R}$,
$n \in \mathbb{N}$, be Borel measurable functions with $f_n(x) \to f(x)$ for almost every
$x \in \mathbb{R}$. Let $g : \mathbb{R} \to \mathbb{R}$ be Lebesgue integrable with
$|f_n(x)| \le g(x)$ for all $n$ and all $x \in \mathbb{R}$. Then for every $\varepsilon > 0$ there
is a Borel set $E \subseteq \mathbb{R}$ of Lebesgue measure less than $\varepsilon$ such that
$f_n \to f$ uniformly on $\mathbb{R} \setminus E$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_43.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_measure_lt_tendstoUniformlyOn_compl_of_ae_tendsto_of_abs_le
  (f : ℝ → ℝ) (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (hfn_meas : ∀ n : ℕ, Measurable (fn n))
  (hae : ∀ᵐ x ∂MeasureTheory.volume, Filter.Tendsto (fun n : ℕ => fn n x) Filter.atTop (nhds (f x)))
  (hg : MeasureTheory.Integrable g)
  (hdom : ∀ n : ℕ, ∀ x : ℝ, |fn n x| ≤ g x) :
  ∀ ε : ℝ, ε > 0 → ∃ E : Set ℝ,
    MeasurableSet E ∧ MeasureTheory.volume E < ENNReal.ofReal ε ∧
      TendstoUniformlyOn fn f Filter.atTop Eᶜ := by
  intro ε hε
  have hf : AEMeasurable f volume :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hfn_meas n).aemeasurable) hae
  have hed (n : ℕ) : AEMeasurable (fun x => edist (fn n x) (f x)) volume :=
    (hfn_meas n).aemeasurable.edist hf
  let B := Egorov.notConvergentSeq fn f
  -- At a fixed error threshold the whole bad set is a.e. contained in a finite-measure level set.
  have hfinite (k : ℕ) : volume (B k 0) ≠ ∞ := by
    have htop := (hg.add hg).measure_norm_gt_lt_top_eNorm
      (ε := (k : ℝ≥0∞)⁻¹) (by simp)
    refine ne_top_of_le_ne_top htop.ne (measure_mono_ae ?_)
    filter_upwards [hae] with x hx
    intro hbad
    obtain ⟨n, -, hn⟩ := Egorov.mem_notConvergentSeq_iff.mp hbad
    change (k : ℝ≥0∞)⁻¹ < ‖(g + g) x‖ₑ
    refine hn.trans_le ?_
    have hf_le := le_of_tendsto hx.abs (Eventually.of_forall fun j => hdom j x)
    have hgnonneg := (abs_nonneg (fn n x)).trans (hdom n x)
    rw [edist_dist, Real.dist_eq, ← ofReal_norm, Pi.add_apply,
      Real.norm_of_nonneg (add_nonneg hgnonneg hgnonneg)]
    apply ENNReal.ofReal_le_ofReal
    calc
      |fn n x - f x| ≤ |fn n x| + |f x| := by simpa using abs_sub_le (fn n x) 0 (f x)
      _ ≤ g x + g x := add_le_add (hdom n x) hf_le
  let b := ENNReal.ofReal (ε / 4)
  have hb : 0 < b := ENNReal.ofReal_pos.mpr (by positivity)
  have hj (k : ℕ) : ∃ j : ℕ, volume (B k j) ≤ b * (2 : ℝ≥0∞)⁻¹ ^ k := by
    obtain ⟨j, hj⟩ := Egorov.exists_notConvergentSeq_lt (μ := volume) (s := B k 0)
      hb hed (Egorov.nullMeasurableSet_notConvergentSeq hed) (hfinite k)
      (hae.mono fun _ hx _ => hx) k
    have hs : B k j ⊆ B k 0 := Egorov.notConvergentSeq_antitone (Nat.zero_le j)
    change volume (B k 0 ∩ B k j) ≤ b * (2 : ℝ≥0∞)⁻¹ ^ k at hj
    rw [inter_eq_right.mpr hs] at hj
    exact ⟨j, hj⟩
  choose j hj using hj
  let U := ⋃ k, B k (j k)
  refine ⟨toMeasurable volume U, measurableSet_toMeasurable _ _, ?_, ?_⟩
  · rw [measure_toMeasurable]
    refine ((measure_iUnion_le _).trans (tsum_le_tsum hj)).trans_lt ?_
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    change ENNReal.ofReal (ε / 4) * 2 < ENNReal.ofReal ε
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  · rw [EMetric.tendstoUniformlyOn_iff]
    intro δ hδ
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
    refine eventually_atTop.2 ⟨j k, fun n hn x hx => ?_⟩
    rw [edist_comm]
    refine (not_lt.mp fun h => hx (subset_toMeasurable volume U ?_)).trans_lt hk
    exact mem_iUnion.2 ⟨k, Egorov.mem_notConvergentSeq_iff.2 ⟨n, hn, h⟩⟩

end MathlibExt.MeasureTheory.EgorovDominatedRealLineWanted
