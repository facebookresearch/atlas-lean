/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.InfinitelyDivisible
public import MathlibExt.Probability.ProbabilityGeneratingFunction
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Galton–Watson branching processes

A Galton–Watson process starts from one individual, and every individual of generation `n`
independently leaves a random number of offspring with law `ν` (the offspring law, a
probability measure on `ℕ`). We describe the process by the laws of its generation sizes:
`law ν 0 = δ₁` and `law ν (n + 1) = (law ν n).bind (Measure.convPow ν)`, where
`Measure.convPow ν z` (from `MathlibExt.Probability.InfinitelyDivisible`) is the `z`-fold
convolution power of `ν` (the law of the total offspring of `z` individuals).

Write `f = pgf id ν` for the offspring generating function `f(s) = ∑ ν{k} s^k` and
`m = ∫⁻ k, k ∂ν ∈ [0, ∞]` for the mean offspring number.

## Main results

* `pgf_law`: the generating function of `Z_n` is the `n`-th iterate `f^[n]` on `[0, 1]`.
* `law_real_zero`: `P(Z_n = 0) = f^[n](0)`.
* `lintegral_law`: `E Z_n = m ^ n`.
* `tendsto_law_real_zero`, `isLeast_extinctionProb`: `P(Z_n = 0)` increases to the extinction
  probability `q`, which is the least fixed point of `f` in `[0, 1]`.
* `extinctionProb_eq_one_iff`: if `ν{1} ≠ 1`, extinction is certain iff `m ≤ 1`.

## References

* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer (1972), ch. I.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MathlibExt.Probability.GaltonWatson

variable (ν : Measure ℕ)

/-- The law of the generation size `Z_n` of the Galton–Watson process with offspring law `ν`
started from one individual: `Z_0 = 1` and, given `Z_n = z`, `Z_{n+1}` has law `ν^{∗z}`
(`Measure.convPow ν z`). -/
noncomputable def law : ℕ → Measure ℕ
  | 0 => Measure.dirac 1
  | n + 1 => (law n).bind (Measure.convPow ν)

/-- The mean offspring number `m = E ξ = ∑ k ν{k} ∈ [0, ∞]`. -/
noncomputable def mean : ℝ≥0∞ :=
  ∫⁻ k, (k : ℝ≥0∞) ∂ν

/-- The extinction probability `q = sup_n P(Z_n = 0)`, the limit of the probabilities of
extinction by generation `n` (`tendsto_law_real_zero`). On a path space carrying the process the
events `{Z_n = 0}` increase with `n` (`0` is absorbing), so `q` is the probability of eventual
extinction; this file describes the process through its generation laws and does not construct
the path space. -/
noncomputable def extinctionProb : ℝ :=
  ⨆ n, (law ν n).real {0}

/-! ### Iterates of the generating function -/

private lemma zero_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩

private theorem pgf_mem [IsProbabilityMeasure ν]
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : pgf id ν s ∈ Icc (0 : ℝ) 1 := by
  have hi := integrable_pow_of_abs_le_one (μ := ν) (s := s) measurable_id
    (by simpa [abs_of_nonneg hs.1] using hs.2)
  refine ⟨integral_nonneg (fun k => pow_nonneg hs.1 k), ?_⟩
  calc
    pgf id ν s ≤ ∫ _ : ℕ, (1 : ℝ) ∂ν :=
      integral_mono hi (integrable_const 1) (fun k => pow_le_one₀ hs.1 hs.2)
    _ = 1 := by simp

private theorem pgf_mono [IsProbabilityMeasure ν] :
    MonotoneOn (pgf id ν) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  exact integral_mono
    (integrable_pow_of_abs_le_one measurable_id (by simpa [abs_of_nonneg hs.1] using hs.2))
    (integrable_pow_of_abs_le_one measurable_id (by simpa [abs_of_nonneg ht.1] using ht.2))
    (fun k => pow_le_pow_left₀ hs.1 hst k)

/-- The iterates `f^[n](s)` of the offspring generating function stay in `[0, 1]` for
`s ∈ [0, 1]`. -/
theorem iterate_pgf_mem_Icc [IsProbabilityMeasure ν] (n : ℕ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : (pgf id ν)^[n] s ∈ Icc (0 : ℝ) 1 := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih (pgf_mem ν hs)

private theorem pgf_tendsto [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} {s : ℝ} (ha : ∀ n, a n ∈ Icc (0 : ℝ) 1)
    (h : Tendsto a atTop (𝓝 s)) :
    Tendsto (fun n => pgf id ν (a n)) atTop (𝓝 (pgf id ν s)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact fun _ => measurable_from_nat.aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact ae_of_all _ fun k => by
      simp only [id_eq, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg (ha n).1 k)]
      exact pow_le_one₀ (ha n).1 (ha n).2
  · exact ae_of_all _ fun k => h.pow k

private theorem iterate_le [IsProbabilityMeasure ν]
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (h : pgf id ν s ≤ s) (n : ℕ) :
    (pgf id ν)^[n] 0 ≤ s := by
  induction n with
  | zero => exact hs.1
  | succ n hn =>
    rw [Function.iterate_succ_apply']
    exact (pgf_mono ν (iterate_pgf_mem_Icc ν n zero_mem) hs hn).trans h

/-- The iterates `f^[n](0)` of the offspring generating function are non-decreasing. -/
theorem monotone_iterate_pgf_zero [IsProbabilityMeasure ν] :
    Monotone fun n => (pgf id ν)^[n] 0 := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa using (pgf_mem ν (by simp : (0 : ℝ) ∈ Icc 0 1)).1
  | succ n hn =>
    simpa only [Function.comp_apply, Function.iterate_succ_apply'] using
      pgf_mono ν (iterate_pgf_mem_Icc ν n zero_mem) (iterate_pgf_mem_Icc ν (n + 1) zero_mem) hn

/-- `sup_n f^[n](0)` is the least fixed point of `f` in `[0, 1]`
(Athreya–Ney 1972, ch. I). -/
theorem isLeast_iSup_iterate_pgf_zero [IsProbabilityMeasure ν] :
    IsLeast {s | s ∈ Icc (0 : ℝ) 1 ∧ pgf id ν s = s} (⨆ n, (pgf id ν)^[n] 0) := by
  have hb : BddAbove (range fun n => (pgf id ν)^[n] 0) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (iterate_pgf_mem_Icc ν n zero_mem).2⟩
  have hq : (⨆ n, (pgf id ν)^[n] 0) ∈ Icc (0 : ℝ) 1 :=
    ⟨(iterate_pgf_mem_Icc ν 0 zero_mem).1.trans (le_ciSup hb 0),
      ciSup_le (fun n => (iterate_pgf_mem_Icc ν n zero_mem).2)⟩
  have ht := tendsto_atTop_ciSup (monotone_iterate_pgf_zero ν) hb
  have hf : pgf id ν (⨆ n, (pgf id ν)^[n] 0) = ⨆ n, (pgf id ν)^[n] 0 := by
    apply tendsto_nhds_unique (pgf_tendsto ν (fun n => iterate_pgf_mem_Icc ν n zero_mem) ht)
    have ht' : Tendsto (fun n => (pgf id ν)^[n + 1] 0) atTop
        (𝓝 (⨆ n, (pgf id ν)^[n] 0)) := ht.comp (tendsto_add_atTop_nat 1)
    simpa only [Nat.add_one, Function.iterate_succ_apply'] using ht'
  refine ⟨⟨hq, hf⟩, ?_⟩
  intro s hs
  exact ciSup_le (iterate_le ν hs.1 hs.2.le)

private def geom (s : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, s ^ j

private theorem geom_nonneg {s : ℝ} (hs : 0 ≤ s) (k : ℕ) : 0 ≤ geom s k := by
  exact Finset.sum_nonneg (fun j _ => pow_nonneg hs j)

private theorem geom_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    geom s k ≤ k := by
  calc
    geom s k ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => pow_le_one₀ hs.1 hs.2)
    _ = k := by simp

private theorem geom_lt {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (k : ℕ) :
    2 ≤ k → geom s k < k := by
  induction k with
  | zero => omega
  | succ k ih =>
    intro hk
    by_cases h : k = 1
    · subst k
      simp only [geom, Finset.sum_range_succ, Finset.sum_range_zero,
        pow_zero, pow_one, zero_add]
      norm_num only [Nat.cast_ofNat]
      linarith [hs.2]
    · have hk' : 2 ≤ k := by omega
      calc
        geom s (k + 1) = geom s k + s ^ k := by simp [geom, Finset.sum_range_succ]
        _ < (k : ℝ) + 1 := add_lt_add_of_lt_of_le (ih hk')
          (pow_le_one₀ hs.1 hs.2.le)
        _ = (k + 1 : ℕ) := by simp

private theorem integrable_geom [IsProbabilityMeasure ν]
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) : Integrable (geom s) ν := by
  refine Integrable.of_bound measurable_from_nat.aestronglyMeasurable
    (1 / (1 - s)) (ae_of_all _ fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (geom_nonneg hs.1 k)]
  apply (le_div_iff₀ (sub_pos.mpr hs.2)).2
  have h := geom_sum_mul_neg s k
  change geom s k * (1 - s) = 1 - s ^ k at h
  rw [h]
  exact sub_le_self _ (pow_nonneg hs.1 k)

private theorem integral_geom [IsProbabilityMeasure ν]
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    (∫ k, geom s k ∂ν) = (1 - pgf id ν s) / (1 - s) := by
  apply (eq_div_iff (sub_pos.mpr hs.2).ne').2
  calc
    (∫ k, geom s k ∂ν) * (1 - s) = ∫ k, geom s k * (1 - s) ∂ν :=
      (integral_mul_const _ _).symm
    _ = ∫ k : ℕ, 1 - s ^ k ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun k => geom_sum_mul_neg s k
    _ = 1 - pgf id ν s := by
      have hi : Integrable (fun k : ℕ => s ^ k) ν :=
        integrable_pow_of_abs_le_one (μ := ν) (s := s) measurable_id
          (by simpa [abs_of_nonneg hs.1] using hs.2.le)
      rw [integral_sub (integrable_const 1) hi]
      simp [pgf]

private theorem lintegral_geom [IsProbabilityMeasure ν]
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    (∫⁻ k, ENNReal.ofReal (geom s k) ∂ν) =
      ENNReal.ofReal ((1 - pgf id ν s) / (1 - s)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_geom ν hs)
    (ae_of_all _ fun k => geom_nonneg hs.1 k), integral_geom ν hs]

private theorem geom_ofReal_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    ENNReal.ofReal (geom s k) ≤ (k : ℝ≥0∞) := by
  exact_mod_cast ENNReal.ofReal_le_ofReal (geom_le hs k)

private theorem fixed_eq_one [IsProbabilityMeasure ν]
    (h1 : ν {1} ≠ 1) (hm : mean ν ≤ 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hf : pgf id ν s = s) : s = 1 := by
  by_contra h
  have hs' : s ∈ Ico (0 : ℝ) 1 := ⟨hs.1, lt_of_le_of_ne hs.2 h⟩
  have hg : (∫⁻ k, ENNReal.ofReal (geom s k) ∂ν) = 1 := by
    rw [lintegral_geom ν hs', hf, div_self (sub_pos.mpr hs'.2).ne']
    simp
  have he := ae_eq_of_ae_le_of_lintegral_le
    (ae_of_all ν fun k => geom_ofReal_le hs k)
    (by rw [hg]; exact ENNReal.one_ne_top)
    (measurable_from_nat.aemeasurable : AEMeasurable (fun k : ℕ => (k : ℝ≥0∞)) ν)
    (by rw [hg]; exact hm)
  have he' : (fun k => ENNReal.ofReal (geom s k)) =ᵐ[ν] ({1} : Set ℕ).indicator 1 := by
    filter_upwards [he] with k hk
    have hreal : geom s k = (k : ℝ) := by
      have ht := congrArg ENNReal.toReal hk
      simpa [ENNReal.toReal_ofReal (geom_nonneg hs.1 k)] using ht
    have hle : k ≤ 1 := by
      by_contra hk'
      exact (ne_of_lt (geom_lt hs' k (by omega))) hreal
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> simp [geom, Set.indicator]
  apply h1
  rw [← lintegral_indicator_one (measurableSet_singleton 1), ← lintegral_congr_ae he', hg]

private theorem mean_le_of_pgf_gt [IsProbabilityMeasure ν]
    (h : ∀ s ∈ Ico (0 : ℝ) 1, s < pgf id ν s) : mean ν ≤ 1 := by
  let a : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have ha : ∀ n, a n ∈ Ico (0 : ℝ) 1 := by
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 0 < (n : ℝ) + 1 := by positivity
    dsimp [a]
    constructor
    · have hd : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hp).2 (by linarith)
      linarith
    · have hd : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have ham : Monotone a := by
    intro n m hnm
    dsimp [a]
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    exact sub_le_sub_left (one_div_le_one_div_of_le hn hnm') 1
  have hat : Tendsto a atTop (𝓝 1) := by
    simpa [a] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hgt : ∀ k, Tendsto (fun n => ENNReal.ofReal (geom (a n) k)) atTop
      (𝓝 (k : ℝ≥0∞)) := by
    intro k
    have hc : Continuous (fun s : ℝ => geom s k) := by unfold geom; fun_prop
    have ht := (ENNReal.continuous_ofReal.tendsto (geom 1 k)).comp
      ((hc.tendsto 1).comp hat)
    change Tendsto (fun n => ENNReal.ofReal (geom (a n) k)) atTop
      (𝓝 (ENNReal.ofReal (geom 1 k))) at ht
    simpa [geom] using ht
  have hi : Tendsto (fun n => ∫⁻ k, ENNReal.ofReal (geom (a n) k) ∂ν)
      atTop (𝓝 (mean ν)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
      (fun _ => measurable_from_nat.aemeasurable)
    · exact ae_of_all _ fun k n m hnm => ENNReal.ofReal_le_ofReal
        (Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (ha n).1 (ham hnm) j))
    · exact ae_of_all _ hgt
  apply le_of_tendsto hi
  exact Filter.Eventually.of_forall fun n => by
    rw [lintegral_geom ν (ha n)]
    apply ENNReal.ofReal_le_one.mpr
    apply (div_le_one (sub_pos.mpr (ha n).2)).2
    linarith [h (a n) (ha n)]

/-- The least fixed point is `1` iff the mean offspring number is at most `1`, provided the
offspring number is not almost surely `1` (Athreya–Ney 1972, ch. I). -/
theorem iSup_iterate_pgf_zero_eq_one_iff [IsProbabilityMeasure ν]
    (h1 : ν {1} ≠ 1) :
    (⨆ n, (pgf id ν)^[n] 0) = 1 ↔ mean ν ≤ 1 := by
  constructor
  · intro hq
    apply mean_le_of_pgf_gt ν
    intro s hs
    by_contra h
    have hle : pgf id ν s ≤ s := le_of_not_gt h
    have hqle : (⨆ n, (pgf id ν)^[n] 0) ≤ s :=
      ciSup_le (iterate_le ν ⟨hs.1, hs.2.le⟩ hle)
    rw [hq] at hqle
    exact (not_le_of_gt hs.2) hqle
  · intro hm
    have hq := (isLeast_iSup_iterate_pgf_zero ν).1
    exact fixed_eq_one ν h1 hm hq.1 hq.2

/-! ### Generation sizes -/

/-- Each generation size has a probability law. -/
instance isProbabilityMeasure_law [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (law ν n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
    rw [law]
    exact isProbabilityMeasure_bind measurable_from_nat.aemeasurable
      (ae_of_all _ fun z => Measure.isProbabilityMeasure_convPow z)

/-- The generating function as a lower integral, `∫⁻ k, s ^ k ∂μ` (proof device). -/
private noncomputable def gen (μ : Measure ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ k, ENNReal.ofReal (s ^ k) ∂μ

private lemma gen_conv {s : ℝ} (hs : 0 ≤ s) (μ ρ : Measure ℕ) [SFinite ρ] :
    gen (μ ∗ ρ) s = gen μ s * gen ρ s := by
  rw [gen, Measure.lintegral_conv measurable_from_nat]
  simp_rw [pow_add, ENNReal.ofReal_mul (pow_nonneg hs _)]
  simp_rw [lintegral_const_mul _ measurable_from_nat]
  rw [lintegral_mul_const _ measurable_from_nat]
  rfl

private lemma gen_convPow [SFinite ν] {s : ℝ} (hs : 0 ≤ s) (z : ℕ) :
    gen (Measure.convPow ν z) s = gen ν s ^ z := by
  induction z with
  | zero => simp [gen, Measure.convPow_zero]
  | succ z ih => rw [Measure.convPow_succ, gen_conv hs, ih, pow_succ]

private lemma gen_le (μ : Measure ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    gen μ s ≤ μ univ :=
  calc gen μ s ≤ ∫⁻ _, 1 ∂μ :=
        lintegral_mono fun _ => ENNReal.ofReal_le_one.2 (pow_le_one₀ hs.1 hs.2)
    _ = μ univ := lintegral_one

private lemma pgf_eq_toReal_gen (μ : Measure ℕ) {s : ℝ} (hs : 0 ≤ s) :
    pgf id μ s = (gen μ s).toReal :=
  integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => pow_nonneg hs _)
    measurable_from_nat.aestronglyMeasurable

private lemma gen_eq_ofReal_pgf (μ : Measure ℕ) [IsFiniteMeasure μ] {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : gen μ s = ENNReal.ofReal (pgf id μ s) := by
  rw [pgf_eq_toReal_gen μ hs.1,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top (measure_ne_top μ univ) (gen_le μ hs))]

private lemma gen_law [IsProbabilityMeasure ν] (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    gen (law ν n) s = ENNReal.ofReal ((pgf id ν)^[n] s) := by
  induction n generalizing s with
  | zero => simp [gen, law, hs.1]
  | succ n ih =>
    have hf := pgf_mem ν hs
    rw [Function.iterate_succ_apply, ← ih hf, law, gen,
      Measure.lintegral_bind measurable_from_nat.aemeasurable measurable_from_nat.aemeasurable]
    change ∫⁻ z, gen (Measure.convPow ν z) s ∂(law ν n) = _
    simp_rw [gen_convPow ν hs.1, gen_eq_ofReal_pgf ν hs, ← ENNReal.ofReal_pow hf.1]
    rfl

/-- The generating function of `Z_n` is the `n`-th iterate of the offspring generating
function on `[0, 1]` (Athreya–Ney 1972, ch. I). -/
theorem pgf_law [IsProbabilityMeasure ν] (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    pgf id (law ν n) s = (pgf id ν)^[n] s := by
  have h := (gen_eq_ofReal_pgf (law ν n) hs).symm.trans (gen_law ν n hs)
  exact (ENNReal.ofReal_eq_ofReal_iff (pgf_mem _ hs).1
    (iterate_pgf_mem_Icc ν n hs).1).1 h

/-- `P(Z_n = 0) = f^[n](0)`. -/
theorem law_real_zero [IsProbabilityMeasure ν] (n : ℕ) :
    (law ν n).real {0} = (pgf id ν)^[n] 0 := by
  rw [← pgf_law ν n zero_mem, pgf_zero id _ measurable_id]
  rfl

private lemma lintegral_convPow [IsProbabilityMeasure ν] (z : ℕ) :
    ∫⁻ k, (k : ℝ≥0∞) ∂(Measure.convPow ν z) = z * mean ν := by
  induction z with
  | zero => simp [Measure.convPow_zero]
  | succ z ih =>
    haveI := Measure.isProbabilityMeasure_convPow (ν := ν) z
    rw [Measure.convPow_succ, Measure.lintegral_conv measurable_from_nat]
    simp_rw [Nat.cast_add]
    simp_rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, ih, mean]
    push_cast
    ring

/-- The mean generation size is `E Z_n = m ^ n` (Athreya–Ney 1972, ch. I). -/
theorem lintegral_law [IsProbabilityMeasure ν] (n : ℕ) :
    ∫⁻ k, (k : ℝ≥0∞) ∂(law ν n) = mean ν ^ n := by
  induction n with
  | zero => simp [law]
  | succ n ih =>
    rw [law, Measure.lintegral_bind measurable_from_nat.aemeasurable
      measurable_from_nat.aemeasurable]
    simp_rw [lintegral_convPow ν]
    rw [lintegral_mul_const _ measurable_from_nat, ih, pow_succ]

/-! ### Extinction -/

/-- `P(Z_n = 0)` is non-decreasing in `n`. -/
theorem monotone_law_real_zero [IsProbabilityMeasure ν] :
    Monotone fun n => (law ν n).real {0} := by
  simp_rw [law_real_zero ν]
  exact monotone_iterate_pgf_zero ν

private lemma extinctionProb_eq_iSup [IsProbabilityMeasure ν] :
    extinctionProb ν = ⨆ n, (pgf id ν)^[n] 0 := by
  simp_rw [extinctionProb, law_real_zero ν]

/-- `P(Z_n = 0)` converges to the extinction probability. -/
theorem tendsto_law_real_zero [IsProbabilityMeasure ν] :
    Tendsto (fun n => (law ν n).real {0}) atTop (𝓝 (extinctionProb ν)) := by
  refine tendsto_atTop_ciSup (monotone_law_real_zero ν) ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact measureReal_le_one

/-- The extinction probability is the least fixed point of the offspring generating function
in `[0, 1]` (Athreya–Ney 1972, ch. I). -/
theorem isLeast_extinctionProb [IsProbabilityMeasure ν] :
    IsLeast {s | s ∈ Icc (0 : ℝ) 1 ∧ pgf id ν s = s} (extinctionProb ν) := by
  rw [extinctionProb_eq_iSup]
  exact isLeast_iSup_iterate_pgf_zero ν

/-- Extinction is certain iff the mean offspring number is at most `1`, provided the offspring
number is not almost surely `1` (Athreya–Ney 1972, ch. I). -/
theorem extinctionProb_eq_one_iff [IsProbabilityMeasure ν] (h1 : ν {1} ≠ 1) :
    extinctionProb ν = 1 ↔ mean ν ≤ 1 := by
  rw [extinctionProb_eq_iSup]
  exact iSup_iterate_pgf_zero_eq_one_iff ν h1

end MathlibExt.Probability.GaltonWatson
