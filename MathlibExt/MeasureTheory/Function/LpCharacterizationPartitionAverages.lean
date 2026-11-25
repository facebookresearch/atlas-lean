/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# L^p on [0,1] via averages over interval partitions

The following OpenBMB notice applies to the adapted declarations and their documentation.

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

Attribution and modification notice: the declarations below are adapted from
openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_02.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_02 … := by sorry` into the Batteries `theorem_wanted`
`memLp_iff_bddAbove_partitionAverageSum`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.MeasureTheory.LpCharacterizationPartitionAveragesWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system; added docstrings to helper definitions.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Characterizing Lp by interval partition averages -/

@[expose] public section

open MeasureTheory Set Filter IsUnifLocDoublingMeasure
open scoped BigOperators ENNReal Topology

namespace MathlibExt.MeasureTheory.LpCharacterizationPartitionAveragesWanted

noncomputable section

/-- **Partitions of the unit interval.** For a natural number $n$, real numbers
$t_0, t_1, \dots, t_n$ form a partition of $[0, 1]$ when $0 = t_0 < t_1 < \dots < t_n = 1$. -/
def IsPartition01 {n : ℕ} (t : Fin (n + 1) → ℝ) : Prop :=
  t 0 = 0 ∧ t (Fin.last n) = 1 ∧ StrictMono t

/-- **Partition average sum.** For a function $f : \mathbb{R} \to \mathbb{R}$, a real number $p$
and real numbers $t_0, t_1, \dots, t_n$, the partition average sum is
$$\sum_{i=0}^{n-1} (t_{i+1} - t_i)
\left(\frac{1}{t_{i+1} - t_i} \int_{[t_i, t_{i+1}]} |f(x)|\,dx\right)^p,$$
where the integrals are Lebesgue integrals over the closed intervals $[t_i, t_{i+1}]$ (empty when
$t_{i+1} < t_i$), the integral of a function that is not integrable there counts as $0$, $1/0 = 0$,
and $0^p$ is taken to be $1$ when $p = 0$ and $0$ when $p \ne 0$. -/
def partitionAverageSum (f : ℝ → ℝ) (p : ℝ) {n : ℕ} (t : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin n,
    let a := t i.castSucc
    let b := t i.succ
    (b - a) * Real.rpow ((1 / (b - a)) * ∫ x in Set.Icc a b, |f x|) p

private def cell {n : ℕ} (t : Fin (n + 1) → ℝ) (i : Fin n) : Set ℝ :=
  Ioc (t i.castSucc) (t i.succ)

private theorem endpoints {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : IsPartition01 t) (i : Fin n) :
    0 ≤ t i.castSucc ∧ t i.castSucc < t i.succ ∧ t i.succ ≤ 1 := by
  refine ⟨?_, ht.2.2 Fin.castSucc_lt_succ, ?_⟩
  · rw [← ht.1]; exact ht.2.2.monotone (Fin.zero_le _)
  · rw [← ht.2.1]; exact ht.2.2.monotone (Fin.le_last _)

private theorem pairwise_cell {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : IsPartition01 t) :
    Pairwise (Function.onFun Disjoint (cell t)) := by
  have h {i j : Fin n} (hij : i < j) : Disjoint (cell t i) (cell t j) := by
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact (not_lt_of_ge (hxi.2.trans (ht.2.2.monotone (Fin.succ_le_castSucc_iff.mpr hij)))) hxj.1
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact h hlt
  · exact (h hgt).symm

private theorem iUnion_cell {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : IsPartition01 t) :
    (⋃ i : Fin n, cell t i) = Ioc 0 1 := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨(endpoints ht i).1.trans_lt hi.1, hi.2.trans (endpoints ht i).2.2⟩
  · intro hx
    let s := Finset.univ.filter fun i : Fin (n + 1) => x ≤ t i
    have hm (i : Fin (n + 1)) : i ∈ s ↔ x ≤ t i := by simp [s]
    have hne : s.Nonempty := ⟨Fin.last n, (hm _).2 (ht.2.1 ▸ hx.2)⟩
    let k := s.min' hne
    have hkm : k ∈ s := Finset.min'_mem s hne
    have hk : k ≠ 0 := by
      intro he
      have h' := (hm k).1 hkm
      rw [he, ht.1] at h'
      exact (not_le_of_gt hx.1) h'
    let i := k.pred hk
    have hik : i.succ = k := Fin.succ_pred k hk
    refine mem_iUnion.mpr ⟨i, ?_, ?_⟩
    · apply lt_of_not_ge
      intro hxi
      have hki := Finset.min'_le s i.castSucc ((hm _).2 hxi)
      have hil : i.castSucc < k := hik ▸ Fin.castSucc_lt_succ
      exact (not_le_of_gt hil) hki
    · rw [hik]; exact (hm k).1 hkm

private def uniform (n : ℕ) (i : Fin (n + 1 + 1)) : ℝ :=
  (i.val : ℝ) / (n + 1 : ℝ)

private theorem uniform_partition (n : ℕ) : IsPartition01 (uniform n) := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  refine ⟨by simp [uniform], by simp [uniform, Nat.cast_succ, hn], ?_⟩
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (by positivity : 0 < (n + 1 : ℝ))).2
  exact_mod_cast (show i.val < j.val from hij)

private theorem uniform_length (n : ℕ) (i : Fin (n + 1)) :
    uniform n i.succ - uniform n i.castSucc = (n + 1 : ℝ)⁻¹ := by
  simp only [uniform, Fin.val_succ, Fin.val_castSucc, Nat.cast_succ]
  rw [← sub_div]
  simp [one_div]

private def avg {n : ℕ} (f : ℝ → ℝ) (t : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  (1 / (t i.succ - t i.castSucc)) * ∫ x in Icc (t i.castSucc) (t i.succ), |f x|

private theorem avg_nonneg {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : IsPartition01 t)
    (f : ℝ → ℝ) (i : Fin n) : 0 ≤ avg f t i := by
  apply mul_nonneg (one_div_nonneg.mpr (sub_nonneg.mpr (endpoints ht i).2.1.le))
  exact setIntegral_nonneg measurableSet_Icc fun _ _ => abs_nonneg _

private theorem avg_eq {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : IsPartition01 t)
    (f : ℝ → ℝ) (i : Fin n) : avg f t i = ⨍ x in cell t i, |f x| := by
  rw [avg, setAverage_eq, Measure.real, cell, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (endpoints ht i).2.1.le), smul_eq_mul,
    one_div, integral_Icc_eq_integral_Ioc]

private theorem jensen_cell {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : IsPartition01 t)
    {f : ℝ → ℝ} {p : ℝ} (hp : 1 ≤ p) (i : Fin n)
    (hf : IntegrableOn (fun x => |f x|) (cell t i))
    (hf' : IntegrableOn (fun x => |f x| ^ p) (cell t i)) :
    (t i.succ - t i.castSucc) * (avg f t i) ^ p ≤ ∫ x in cell t i, |f x| ^ p := by
  have hl : 0 < t i.succ - t i.castSucc := sub_pos.mpr (endpoints ht i).2.1
  have hm : (volume : Measure ℝ) (cell t i) = ENNReal.ofReal (t i.succ - t i.castSucc) :=
    Real.volume_Ioc
  have hj : (⨍ x in cell t i, |f x|) ^ p ≤ ⨍ x in cell t i, |f x| ^ p :=
    (convexOn_rpow hp).map_set_average_le
      (Real.continuous_rpow_const (zero_le_one.trans hp)).continuousOn isClosed_Ici
      (by rw [hm]; exact (ENNReal.ofReal_pos.mpr hl).ne') (hm ▸ ENNReal.ofReal_ne_top)
      (Eventually.of_forall fun x => abs_nonneg (f x)) hf hf'
  rw [← avg_eq ht f i, setAverage_eq, Measure.real, hm, ENNReal.toReal_ofReal hl.le,
    smul_eq_mul, ← div_eq_inv_mul] at hj
  rw [mul_comm]
  exact (le_div_iff₀ hl).mp hj

private def steps (f : ℝ → ℝ) (p : ℝ) (n : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑ i : Fin (n + 1), (cell (uniform n) i).indicator
    (fun _ => ENNReal.ofReal ((avg f (uniform n) i) ^ p)) x

private theorem steps_measurable (f : ℝ → ℝ) (p : ℝ) (n : ℕ) : Measurable (steps f p n) := by
  unfold steps
  exact Finset.measurable_fun_sum _ fun i _ => measurable_const.indicator
    (show MeasurableSet (cell (uniform n) i) from measurableSet_Ioc)

private theorem steps_at_cell (f : ℝ → ℝ) (p : ℝ) {n : ℕ} {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ cell (uniform n) i) :
    steps f p n x = ENNReal.ofReal ((avg f (uniform n) i) ^ p) := by
  unfold steps
  rw [Finset.sum_eq_single i, indicator_of_mem hx]
  · intro j _ hji
    exact indicator_of_notMem
      (Set.disjoint_left.mp (pairwise_cell (uniform_partition n) hji.symm) hx) _
  · simp

private theorem steps_integral (f : ℝ → ℝ) (p : ℝ) (n : ℕ) :
    (∫⁻ x in Ioc 0 1, steps f p n x) =
      ENNReal.ofReal (∑ i : Fin (n + 1),
        (uniform n i.succ - uniform n i.castSucc) * (avg f (uniform n) i) ^ p) := by
  have hs (i : Fin (n + 1)) : cell (uniform n) i ⊆ Ioc 0 1 :=
    fun _ hx => ⟨(endpoints (uniform_partition n) i).1.trans_lt hx.1,
      hx.2.trans (endpoints (uniform_partition n) i).2.2⟩
  simp only [steps]
  rw [lintegral_finsetSum (f := fun (i : Fin (n + 1)) x => (cell (uniform n) i).indicator
      (fun _ => ENNReal.ofReal ((avg f (uniform n) i) ^ p)) x) _
      (fun i _ => measurable_const.indicator
        (show MeasurableSet (cell (uniform n) i) from measurableSet_Ioc)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg
      (sub_nonneg.mpr (endpoints (uniform_partition n) i).2.1.le)
      (Real.rpow_nonneg (avg_nonneg (uniform_partition n) f i) _))]
  apply Finset.sum_congr rfl
  intro i _
  have hmeas : MeasurableSet (cell (uniform n) i) := measurableSet_Ioc
  rw [lintegral_indicator_const hmeas, Measure.restrict_apply hmeas, inter_eq_left.mpr (hs i),
    cell, Real.volume_Ioc,
    ENNReal.ofReal_mul (sub_nonneg.mpr (endpoints (uniform_partition n) i).2.1.le), mul_comm]

private theorem ae_steps_tendsto {f : ℝ → ℝ} {p : ℝ} (hp : 0 ≤ p)
    (hf : IntegrableOn (fun x => |f x|) (Icc 0 1)) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioc 0 1)),
      Tendsto (fun n => steps f p n x) atTop (𝓝 (ENNReal.ofReal (|f x| ^ p))) := by
  let g := (Icc (0 : ℝ) 1).indicator (fun x => |f x|)
  let v := vitaliFamily (volume : Measure ℝ) 1
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Icc
  have hdiff := (v.ae_tendsto_average hg.locallyIntegrable).filter_mono
    (ae_mono (Measure.restrict_le_self (s := Ioc (0 : ℝ) 1)))
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hdiff] with x hx hx_diff
  have hcells (n : ℕ) : ∃ i : Fin (n + 1), x ∈ cell (uniform n) i := by
    apply mem_iUnion.mp
    rwa [iUnion_cell (uniform_partition n)]
  let i (n : ℕ) := (hcells n).choose
  have hi (n : ℕ) : x ∈ cell (uniform n) (i n) := (hcells n).choose_spec
  let a (n : ℕ) := uniform n (i n).castSucc
  let b (n : ℕ) := uniform n (i n).succ
  have hab (n : ℕ) : 0 ≤ a n ∧ a n < b n ∧ b n ≤ 1 := endpoints (uniform_partition n) (i n)
  have hmem (n : ℕ) : x ∈ Icc (a n) (b n) := ⟨(hi n).1.le, (hi n).2⟩
  have hlen : Tendsto (fun n : ℕ => b n - a n) atTop (𝓝 0) := by
    simp_rw [a, b, uniform_length]
    simpa only [Function.comp_def, Nat.cast_succ] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
        ((tendsto_add_atTop_iff_nat 1).2 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlocal : Tendsto (fun n => Icc (a n) (b n)) atTop (v.filterAt x) := by
    apply v.tendsto_filterAt_iff.mpr
    constructor
    · filter_upwards with n
      change Icc (a n) (b n) ∈ (vitaliFamily (volume : Measure ℝ) 1).setsAt x
      rw [Real.Icc_eq_closedBall]
      refine closedBall_mem_vitaliFamily_of_dist_le_mul _ ?_ (by linarith [(hab n).2.1])
      rw [Real.dist_eq, one_mul, abs_le]
      exact ⟨by linarith [(hmem n).1], by linarith [(hmem n).2]⟩
    · intro ε hε
      filter_upwards [(tendsto_order.1 hlen).2 ε hε] with n hn
      rw [Real.closedBall_eq_Icc]
      exact Icc_subset_Icc (by linarith [(hmem n).2]) (by linarith [(hmem n).1])
  have hxeq : g x = |f x| := indicator_of_mem (Ioc_subset_Icc_self hx) _
  have havg : Tendsto (fun n => avg f (uniform n) (i n)) atTop (𝓝 |f x|) := by
    rw [← hxeq]
    apply Tendsto.congr' _ (hx_diff.comp hlocal)
    filter_upwards with n
    have hset : Icc (a n) (b n) ⊆ Icc 0 1 := Icc_subset_Icc (hab n).1 (hab n).2.2
    have heq : (∫ y in Icc (a n) (b n), g y) = ∫ y in Icc (a n) (b n), |f y| :=
      setIntegral_congr_fun measurableSet_Icc (fun y hy => indicator_of_mem (hset hy) _)
    change (⨍ y in Icc (a n) (b n), g y) = avg f (uniform n) (i n)
    rw [setAverage_eq, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (hab n).2.1.le), smul_eq_mul, heq]
    simp only [avg, one_div, a, b]
  have hconv := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((Real.continuous_rpow_const hp).continuousAt.tendsto.comp havg)
  exact hconv.congr (fun n => (steps_at_cell f p (hi n)).symm)

/-- **$L^p$ on $[0,1]$ via averages over partitions.** Let $f : \mathbb{R} \to \mathbb{R}$ be in
$L^1([0, 1])$ and let $p > 1$ be a real number. Then $f \in L^p([0, 1])$ if and only if there is
a real number $C$ such that
$$\sum_{i=0}^{n-1} (t_{i+1} - t_i)
\left(\frac{1}{t_{i+1} - t_i} \int_{t_i}^{t_{i+1}} |f(x)|\,dx\right)^p \le C$$
for every partition $0 = t_0 < t_1 < \dots < t_n = 1$ of $[0, 1]$. Here $L^1([0, 1])$ and
$L^p([0, 1])$ are taken with respect to Lebesgue measure restricted to $[0, 1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_02.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem memLp_iff_bddAbove_partitionAverageSum
    (f : ℝ → ℝ) (p : ℝ)
    (hp : 1 < p)
    (hf_L1 : MemLp f 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ↔
      ∃ C : ℝ, ∀ n : ℕ, ∀ t : Fin (n + 1) → ℝ,
        IsPartition01 t →
          partitionAverageSum f p t ≤ C := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hf : IntegrableOn (fun x => |f x|) (Icc 0 1) := by
    rw [IntegrableOn]
    simpa only [Real.norm_eq_abs] using (memLp_one_iff_integrable.mp hf_L1).norm
  have hμ : (volume : Measure ℝ).restrict (Ioc 0 1) = volume.restrict (Icc 0 1) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  constructor
  · intro h
    have hpint : IntegrableOn (fun x => |f x| ^ p) (Ioc 0 1) := by
      rw [IntegrableOn, hμ]
      simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
        (integrable_norm_rpow_iff h.aestronglyMeasurable hpne ENNReal.ofReal_ne_top).mpr h
    refine ⟨∫ x in Ioc 0 1, |f x| ^ p, fun n t ht => ?_⟩
    have hsub (i : Fin n) : cell t i ⊆ Ioc 0 1 :=
      fun _ hx => ⟨(endpoints ht i).1.trans_lt hx.1, hx.2.trans (endpoints ht i).2.2⟩
    have hcell (i : Fin n) := hpint.mono_set (hsub i)
    calc
      _ ≤ ∑ i : Fin n, ∫ x in cell t i, |f x| ^ p := by
        refine Finset.sum_le_sum fun i _ => jensen_cell ht hp.le i ?_ (hcell i)
        exact hf.mono_set ((hsub i).trans Ioc_subset_Icc_self)
      _ = ∫ x in Ioc 0 1, |f x| ^ p := by
        rw [← integral_iUnion_fintype
          (fun i => (show MeasurableSet (cell t i) from measurableSet_Ioc))
          (pairwise_cell ht) hcell, iUnion_cell ht]
  · rintro ⟨C, hC⟩
    have hbound (n : ℕ) : (∫⁻ x in Ioc 0 1, steps f p n x) ≤ ENNReal.ofReal C := by
      rw [steps_integral]
      exact ENNReal.ofReal_le_ofReal (hC (n + 1) (uniform n) (uniform_partition n))
    have hlim : (fun x => liminf (fun n => steps f p n x) atTop) =ᵐ[
        (volume : Measure ℝ).restrict (Ioc 0 1)] (fun x => ENNReal.ofReal (|f x| ^ p)) :=
      (ae_steps_tendsto hp0.le hf).mono fun _ h => h.liminf_eq
    have hfinite : (∫⁻ x in Ioc 0 1, ENNReal.ofReal (|f x| ^ p)) < ⊤ := by
      rw [← lintegral_congr_ae hlim]
      refine (lintegral_liminf_le (steps_measurable f p)).trans_lt ?_
      exact (liminf_le_of_frequently_le (Eventually.of_forall hbound).frequently).trans_lt
        ENNReal.ofReal_lt_top
    rw [memLp_iff]
    apply (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hpne ENNReal.ofReal_ne_top
      hf_L1.aestronglyMeasurable).2
    rw [hμ] at hfinite
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.eNorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le] using hfinite

end

end MathlibExt.MeasureTheory.LpCharacterizationPartitionAveragesWanted
