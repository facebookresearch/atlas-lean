/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import MathlibExt.Probability.ContinuousDistributions
public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.Statistics.MultipleTesting.Bonferroni
public import MathlibExt.Probability.Statistics.NormalTheory
public import MathlibExt.Probability.Statistics.NormalTheoryTwoSample
import MathlibExt.Probability.Statistics.SampleMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Statistical treatment of analytical data

Descriptive statistics, t-intervals with exact coverage, pooled variance, F and t statistics,
outlier-test procedures, and detection-limit conventions for quantitative analysis.

## i. Overview

This module collects the statistical toolkit of analytical chemistry on the canonical ATLAS
statistics API. The sample mean and the Bessel-corrected sample variance are
`MathlibExt.Probability.FiniteProbability.sampleMean` and `sampleVarUnbiased`; this module adds
the data-level sample standard deviation `sampleStdDev` (the random-variable version
`MathlibExt.Probability.ContinuousDistributions.sampleStdDev` is this applied to the first `n`
observations, `sampleStdDev_eq_of_seq`) and facts about constant samples and `n = 1`.

The two-sided t-interval `x̄ ± t s / √n` (`tInterval`; the random-variable version
`ContinuousDistributions.studentTInterval` is this on the first `n` observations,
`studentTInterval_eq_tInterval`) covers the mean of an i.i.d. normal sample with probability
exactly `1 - α` when `t` is the upper `α/2` point of Student's t law on `n - 1` degrees of
freedom (`tInterval_coverage`, which restates
`ProbabilityTheory.one_sample_t_interval_coverage_eq`).

The pooled variance, the pooled two-sample t statistic and the variance ratio are the canonical
`ProbabilityTheory.pooledVariance`, `twoSampleTStatistic` and `varianceRatio` of
`MathlibExt.Probability.Statistics.NormalTheoryTwoSample`, which also proves their exact laws for
independent normal samples (`hasLaw_twoSampleTStatistic`, `hasLaw_varianceRatio`). This module
adds the weighted form of the pooled variance (`pooledVariance_eq_weighted`) and its
unbiasedness without normality (`integral_pooledVariance`): for two samples, each pairwise
independent and identically distributed with finite second moment, with equal variances, from
`MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin`.

The Dixon Q and Grubbs statistics are computed from the whole sample: Dixon's Q for observation
`j` is the gap to its nearest other observation over the sample range, and Grubbs' G is the
largest absolute deviation from the sample mean over the sample standard deviation. The decision
procedures compare them with nonnegative caller-supplied critical values, Dixon's procedure
rejects only an extreme observation, and a sample without spread is never rejected
(`not_dixonReject_of_no_spread`, `not_grubbsReject_of_sd_zero`). No error-rate claim is made for
these procedures, nor for the `k = 3` and `k = 3.3` detection-limit conventions, which are stated
conventions. The Bonferroni level `α / m` is the threshold of the canonical
`MathlibExt.Probability.Statistics.MultipleTesting.bonferroniRejections`
(`mem_bonferroniRejections_iff`), whose family-wise error control is
`MultipleTesting.measure_bonferroni_familywiseError_le`.

Several formulas divide by a quantity that can vanish; each docstring states the domain on which
the formula is meaningful. Dixon's Q and Grubbs' G are defined to be `0` when the spread is `0`.

## ii. Key results

- `sampleMean_const`, `sampleVarUnbiased_nonneg`, `sampleVarUnbiased_const`,
  `sampleVarUnbiased_fin_one`, `sampleStdDev_const`: constant samples, nonnegativity for
  `2 ≤ n`, and the degenerate value `0` at `n = 1`.
- `sampleStdDev_eq_of_seq`, `studentTInterval_eq_tInterval`: bridges to the random-variable API
  of `ContinuousDistributions`.
- `tHalfWidth_nonneg`, `mem_tInterval_iff`: the t half-width and the membership duality.
- `tInterval_coverage`: exact coverage `1 - α` of the t-interval for i.i.d. normal samples.
- `pooledVariance_eq_weighted`, `pooledVariance_nonneg`, `varianceRatio_nonneg`: the canonical
  pooled variance as a weighted average of the sample variances, and nonnegativity.
- `integral_pooledVariance`: the pooled variance is unbiased under the equal-variance model.
- `dixonQ_of_ne`, `dixonQ_of_no_spread`, `dixonQ_nonneg`, `dixonReject_mono`,
  `not_dixonReject_of_no_spread`: Dixon's Q and its decision procedure.
- `grubbsG_of_ne`, `grubbsG_of_sd_zero`, `grubbsG_nonneg`, `div_le_grubbsG`,
  `exists_grubbsG_eq`, `grubbsReject_mono`, `not_grubbsReject_of_sd_zero`: Grubbs' G is the
  largest standardized residual.
- `mem_bonferroniRejections_iff`, `bonferroniLevel_nonneg`, `lodK3_nonneg`, `lodK33_nonneg`: the
  Bonferroni level of the canonical procedure, and the detection-limit conventions.

## iii. Table of contents

- A. Sample mean, variance, and standard deviation
- B. t-intervals and their exact coverage
- C. Pooled variance and two-sample statistics
- D. Outlier procedures: Dixon Q and Grubbs
- E. Multiplicity adjustment and detection limits

## iv. References

- JCGM 100:2008, _Guide to the Expression of Uncertainty in Measurement_ (GUM)
  (uncertainty evaluation and propagation).
- OpenStax, _Chemistry 2e_ (descriptive statistics and analytical-chemistry
  procedures).
- IUPAC, _Quantities, Units and Symbols in Physical Chemistry_ (Green Book),
  abridged 4th edition (RSC, 2023) (quantity and unit conventions).
- ATLAS statistics API: `MathlibExt.Probability.FiniteProbability` (sample mean and
  variance), `MathlibExt.Probability.Statistics.SampleMoments` (unbiasedness of the sample
  variance), `MathlibExt.Probability.Statistics.NormalTheory` (exact t-interval coverage),
  `MathlibExt.Probability.Statistics.NormalTheoryTwoSample` (pooled variance, two-sample t,
  variance ratio), `MathlibExt.Probability.ContinuousDistributions` (random-variable t-interval)
  and `MathlibExt.Probability.Statistics.MultipleTesting.Bonferroni`.

## A. Sample mean, variance, and standard deviation
-/

@[expose] public section

namespace Chemistry.StatisticalTreatment

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.FiniteProbability (sampleMean sampleVarUnbiased sampleMean_eq_sum_div
  sampleVarUnbiased_eq_sum_div)

/-- The mean of a constant sample is the constant. -/
lemma sampleMean_const (n : ℕ) (hn : n ≠ 0) (c : ℝ) (x : Fin n → ℝ)
    (h : ∀ i, x i = c) : sampleMean x = c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [sampleMean_eq_sum_div, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  field_simp

/-- The sample variance `∑ (xᵢ - x̄)² / (n - 1)` is nonnegative for `2 ≤ n`. -/
lemma sampleVarUnbiased_nonneg (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ) :
    0 ≤ sampleVarUnbiased x := by
  rw [sampleVarUnbiased_eq_sum_div, Fintype.card_fin]
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by linarith)

/-- Constant samples have zero sample variance. -/
lemma sampleVarUnbiased_const (n : ℕ) (hn : n ≠ 0) (c : ℝ) (x : Fin n → ℝ)
    (h : ∀ i, x i = c) : sampleVarUnbiased x = 0 := by
  rw [sampleVarUnbiased_eq_sum_div, sampleMean_const n hn c x h,
    Finset.sum_eq_zero (fun i _ => by rw [h i, sub_self, sq, mul_zero]), zero_div]

/-- At `n = 1` the Bessel denominator `n - 1` vanishes and Lean's division gives `0`: the sample
variance of one observation carries no information, and no t-procedure applies. -/
lemma sampleVarUnbiased_fin_one (x : Fin 1 → ℝ) : sampleVarUnbiased x = 0 := by
  rw [sampleVarUnbiased_eq_sum_div, Fintype.card_fin]
  norm_num

/-- Sample standard deviation `s = √s²`, from the canonical unbiased sample variance. -/
noncomputable def sampleStdDev {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (sampleVarUnbiased x)

/-- The sample standard deviation is nonnegative. -/
lemma sampleStdDev_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ sampleStdDev x :=
  Real.sqrt_nonneg _

/-- Constant samples have zero standard deviation. -/
lemma sampleStdDev_const (n : ℕ) (hn : n ≠ 0) (c : ℝ) (x : Fin n → ℝ)
    (h : ∀ i, x i = c) : sampleStdDev x = 0 := by
  unfold sampleStdDev
  rw [sampleVarUnbiased_const n hn c x h, Real.sqrt_zero]

/-- The random-variable sample standard deviation of `ContinuousDistributions` is
`sampleStdDev` of the first `n` observations. -/
lemma sampleStdDev_eq_of_seq {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    MathlibExt.Probability.ContinuousDistributions.sampleStdDev X n ω =
      sampleStdDev (fun i : Fin n => X i ω) :=
  rfl

/-! ## B. t-intervals and their exact coverage -/

/-- Half-width `tcrit * s / √n` of a t-interval, meaningful for `n ≥ 1` (at `n = 0` Lean's
division returns `0`). -/
noncomputable def tHalfWidth (s : ℝ) (n : ℕ) (tcrit : ℝ) : ℝ :=
  tcrit * s / Real.sqrt (n : ℝ)

/-- The half-width is nonnegative for nonnegative critical value and scale. -/
lemma tHalfWidth_nonneg (s : ℝ) (n : ℕ) (tcrit : ℝ) (ht : 0 ≤ tcrit)
    (hs : 0 ≤ s) : 0 ≤ tHalfWidth s n tcrit := by
  unfold tHalfWidth
  exact div_nonneg (mul_nonneg ht hs) (Real.sqrt_nonneg _)

/-- The t-interval `x̄ ± tcrit * s / √n` as a set. Its exact coverage under i.i.d. normal sampling,
with the sample mean, the sample standard deviation and the Student-t quantile, is
`tInterval_coverage`. -/
def tInterval (xbar s : ℝ) (n : ℕ) (tcrit : ℝ) : Set ℝ :=
  Set.Icc (xbar - tHalfWidth s n tcrit) (xbar + tHalfWidth s n tcrit)

/-- A value lies in the t-interval iff it is within one half-width of the mean (pure algebra). -/
lemma mem_tInterval_iff (xbar s : ℝ) (n : ℕ) (tcrit μ : ℝ) :
    μ ∈ tInterval xbar s n tcrit ↔ |xbar - μ| ≤ tHalfWidth s n tcrit := by
  unfold tInterval
  rw [Set.mem_Icc]
  constructor
  · intro h
    obtain ⟨hlo, hhi⟩ := h
    rw [abs_le]
    constructor <;> linarith
  · intro h
    rw [abs_le] at h
    obtain ⟨hlo, hhi⟩ := h
    constructor <;> linarith

/-- The random-variable t-interval of `ContinuousDistributions` is `tInterval` computed from the
first `n` observations. Its coverage under `ContinuousDistributions.StudentTPivotLaw` is
`StudentTPivotLaw.measureReal_mem_studentTInterval`. -/
lemma studentTInterval_eq_tInterval {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (q : ℝ) (ω : Ω) :
    MathlibExt.Probability.ContinuousDistributions.studentTInterval X n q ω =
      tInterval (sampleMean fun i : Fin n => X i ω) (sampleStdDev fun i : Fin n => X i ω) n q :=
  rfl

/-- **Exact coverage of the two-sided t-interval.** For an i.i.d. `N(μ, v)` sample `X` of size
`n ≥ 2` with `v ≠ 0` and `α ∈ (0, 1)`, let `t = cdfQuantile (t_{n-1}) (1 - α/2)` be the upper
`α/2` point of Student's t law on `n - 1` degrees of freedom. The t-interval built from the sample
mean and the sample standard deviation covers `μ` with probability exactly `1 - α`. This is
`ProbabilityTheory.one_sample_t_interval_coverage_eq` restated with `tInterval`, `sampleMean` and
`sampleStdDev`. -/
theorem tInterval_coverage {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal} (hv : v ≠ 0) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Fin n → ℝ} (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    P.real {ω | μ ∈ tInterval (sampleMean (X ω)) (sampleStdDev (X ω)) n
      (cdfQuantile (studentTMeasure (n - 1)) (1 - α / 2))} = 1 - α := by
  rw [← one_sample_t_interval_coverage_eq hn μ hv hα hX]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, mem_tInterval_iff, tHalfWidth, sampleStdDev,
    sampleVarUnbiased_eq_sum_div, sampleMean_eq_sum_div, Fintype.card_fin]

/-! ## C. Pooled variance and two-sample statistics

The pooled variance `S_p² = (∑ (xᵢ - x̄)² + ∑ (yⱼ - ȳ)²) / (m + n - 2)`, the pooled two-sample t
statistic and the variance ratio `S_x² / S_y²` are `ProbabilityTheory.pooledVariance`,
`ProbabilityTheory.twoSampleTStatistic` (the chemists' statistic is `twoSampleTStatistic 0`) and
`ProbabilityTheory.varianceRatio`; their exact laws for independent normal samples are in
`MathlibExt.Probability.Statistics.NormalTheoryTwoSample`. -/

/-- For `m, n ≥ 2` the pooled variance is the weighted average
`((m - 1) s_x² + (n - 1) s_y²) / (m + n - 2)` of the two unbiased sample variances. -/
theorem pooledVariance_eq_weighted {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (x : Fin m → ℝ)
    (y : Fin n → ℝ) :
    pooledVariance x y =
      (((m : ℝ) - 1) * sampleVarUnbiased x + ((n : ℝ) - 1) * sampleVarUnbiased y) /
        ((m : ℝ) + n - 2) := by
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [pooledVariance_eq_sampleMean, sampleVarUnbiased_eq_sum_div, sampleVarUnbiased_eq_sum_div,
    Fintype.card_fin, Fintype.card_fin]
  congr 1
  field_simp

/-- The pooled variance is nonnegative for `m, n ≥ 2`. -/
lemma pooledVariance_nonneg {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (x : Fin m → ℝ)
    (y : Fin n → ℝ) : 0 ≤ pooledVariance x y := by
  rw [pooledVariance_eq_sampleMean]
  have h2m : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Finset.sum_nonneg fun j _ => sq_nonneg _)) (by linarith)

/-- **The pooled variance is unbiased under the equal-variance model.** Let `X i`, `i : Fin m`,
and `Y j`, `j : Fin n`, with `m, n ≥ 2`, be two samples on a probability space. Each sample is
pairwise independent and identically distributed (common laws those of `X i0` and `Y j0`) with
finite second moment, and the two variances are equal: `Var Y j0 = Var X i0`, the
equal-variance model hypothesis. Then the pooled variance of the two samples is integrable and
its expectation is the common variance. No normality and no independence between the two samples
are needed: each sample variance is unbiased
(`MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin`), and the pooled variance
is their weighted average (`pooledVariance_eq_weighted`). -/
theorem integral_pooledVariance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (X : Fin m → Ω → ℝ) (Y : Fin n → Ω → ℝ) (i0 : Fin m) (j0 : Fin n)
    (hXind : Pairwise fun i j => X i ⟂ᵢ[P] X j) (hXid : ∀ i, IdentDistrib (X i) (X i0) P P)
    (hX2 : MemLp (X i0) 2 P)
    (hYind : Pairwise fun i j => Y i ⟂ᵢ[P] Y j) (hYid : ∀ j, IdentDistrib (Y j) (Y j0) P P)
    (hY2 : MemLp (Y j0) 2 P) (hvar : variance (Y j0) P = variance (X i0) P) :
    Integrable (fun ω => pooledVariance (fun i => X i ω) (fun j => Y j ω)) P ∧
    ∫ ω, pooledVariance (fun i => X i ω) (fun j => Y j ω) ∂P = variance (X i0) P := by
  obtain ⟨iX, eX⟩ :=
    MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin hm X i0 hXind hXid hX2
  obtain ⟨iY, eY⟩ :=
    MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin hn Y j0 hYind hYid hY2
  have hD : (m : ℝ) + n - 2 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp_rw [pooledVariance_eq_weighted hm hn]
  refine ⟨((iX.const_mul _).add (iY.const_mul _)).div_const _, ?_⟩
  rw [integral_div, integral_add (iX.const_mul _) (iY.const_mul _), integral_const_mul,
    integral_const_mul, eX, eY, hvar]
  field_simp
  ring

/-- The variance ratio `S_x² / S_y²` is nonnegative for `m, n ≥ 2`. -/
lemma varianceRatio_nonneg {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (x : Fin m → ℝ)
    (y : Fin n → ℝ) : 0 ≤ varianceRatio x y := by
  rw [varianceRatio_eq]
  exact div_nonneg (sampleVarUnbiased_nonneg m hm x) (sampleVarUnbiased_nonneg n hn y)

/-! ## D. Outlier procedures: Dixon Q and Grubbs -/

/-- The range `max x - min x` of a sample. For the empty sample Lean's `⨆` and `⨅` over an empty
family are `0`, so the range is `0`. -/
noncomputable def sampleRange {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (⨆ i, x i) - ⨅ i, x i

/-- The sample range is nonnegative. -/
lemma sampleRange_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ sampleRange x := by
  unfold sampleRange
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · rw [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty, sub_self]
  · exact sub_nonneg.mpr
      (ciInf_le_ciSup (Set.finite_range x).bddBelow (Set.finite_range x).bddAbove)

/-- The gap `min_{i ≠ j} |x j - x i|` from observation `j` to its nearest other observation. For
a one-point sample the infimum is over an empty family and is `0`. -/
noncomputable def nearestGap {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  ⨅ i : {i : Fin n // i ≠ j}, |x j - x i|

/-- The nearest-neighbour gap is nonnegative. -/
lemma nearestGap_nonneg {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : 0 ≤ nearestGap x j :=
  Real.iInf_nonneg fun _ => abs_nonneg _

/-- Observation `j` is extreme: it is the sample maximum or the sample minimum. -/
def IsExtremeObservation {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : Prop :=
  x j = (⨆ i, x i) ∨ x j = ⨅ i, x i

/-- Dixon's Q statistic for observation `j` of the sample `x`: the gap to the nearest other
observation over the sample range, `nearestGap x j / sampleRange x`, and `0` when the range is
`0` (no spread, hence no rejection). Dixon's procedure applies it to an extreme observation
(`IsExtremeObservation`, which `dixonReject` requires). Tabulated critical values, and any
error-rate meaning of the comparison, assume i.i.d. normal sampling, which is not modelled
here. -/
noncomputable def dixonQ {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  if sampleRange x = 0 then 0 else nearestGap x j / sampleRange x

/-- Unfolding of `dixonQ` away from the degenerate case. -/
lemma dixonQ_of_ne {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (h : sampleRange x ≠ 0) :
    dixonQ x j = nearestGap x j / sampleRange x := by
  rw [dixonQ, ite_eq_right h]

/-- With no spread the Dixon statistic is `0`. -/
lemma dixonQ_of_no_spread {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (h : sampleRange x = 0) :
    dixonQ x j = 0 := by
  rw [dixonQ, ite_eq_left h]

/-- Dixon's Q is nonnegative. -/
lemma dixonQ_nonneg {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : 0 ≤ dixonQ x j := by
  unfold dixonQ
  split_ifs
  · exact le_rfl
  · exact div_nonneg (nearestGap_nonneg x j) (sampleRange_nonneg x)

/-- Dixon decision procedure: reject observation `j` at the critical value `qcrit ≥ 0` when it is
extreme and its Q statistic exceeds `qcrit`. The critical value is an explicit nonnegative input
(tabulated values assume normality); a negative `qcrit` never rejects. -/
def dixonReject {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (qcrit : ℝ) : Prop :=
  IsExtremeObservation x j ∧ 0 ≤ qcrit ∧ qcrit < dixonQ x j

/-- Rejection is monotone in the critical value: a smaller nonnegative threshold rejects whenever
a larger one does. -/
lemma dixonReject_mono {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (qa qb : ℝ) (hb : 0 ≤ qb)
    (h : qb ≤ qa) (r : dixonReject x j qa) : dixonReject x j qb :=
  ⟨r.1, hb, lt_of_le_of_lt h r.2.2⟩

/-- A sample without spread is never rejected by Dixon's procedure, at any critical value. -/
lemma not_dixonReject_of_no_spread {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (h : sampleRange x = 0)
    (qcrit : ℝ) : ¬ dixonReject x j qcrit := by
  rintro ⟨-, hq, hlt⟩
  rw [dixonQ_of_no_spread x j h] at hlt
  exact absurd hlt (not_lt.mpr hq)

/-- Grubbs' statistic `G = max_i |x i - x̄| / s` of a sample: the largest absolute deviation from
the sample mean over the sample standard deviation, and `0` when `s = 0` (no spread, hence no
rejection). The maximum is over the whole sample (`div_le_grubbsG`) and is attained by an
observation (`exists_grubbsG_eq`). Tabulated critical values assume i.i.d. normal sampling,
which is not modelled here. -/
noncomputable def grubbsG {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  if sampleStdDev x = 0 then 0 else (⨆ i, |x i - sampleMean x|) / sampleStdDev x

/-- Unfolding of `grubbsG` away from the degenerate case. -/
lemma grubbsG_of_ne {n : ℕ} (x : Fin n → ℝ) (h : sampleStdDev x ≠ 0) :
    grubbsG x = (⨆ i, |x i - sampleMean x|) / sampleStdDev x := by
  rw [grubbsG, ite_eq_right h]

/-- With zero spread the Grubbs statistic is `0`: degenerate input produces no rejection at any
nonnegative critical value. -/
lemma grubbsG_of_sd_zero {n : ℕ} (x : Fin n → ℝ) (h : sampleStdDev x = 0) : grubbsG x = 0 := by
  rw [grubbsG, ite_eq_left h]

/-- The Grubbs statistic is nonnegative. -/
lemma grubbsG_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ grubbsG x := by
  unfold grubbsG
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _) (sampleStdDev_nonneg x)

/-- Every standardized residual `|x i - x̄| / s` is at most Grubbs' statistic. -/
lemma div_le_grubbsG {n : ℕ} (x : Fin n → ℝ) (h : sampleStdDev x ≠ 0) (i : Fin n) :
    |x i - sampleMean x| / sampleStdDev x ≤ grubbsG x := by
  rw [grubbsG_of_ne x h]
  exact div_le_div_of_nonneg_right
    (le_ciSup (f := fun i => |x i - sampleMean x|) (Set.finite_range _).bddAbove i)
    (sampleStdDev_nonneg x)

/-- Grubbs' statistic is the standardized residual of some observation. -/
lemma exists_grubbsG_eq {n : ℕ} (x : Fin n → ℝ) (h : sampleStdDev x ≠ 0) :
    ∃ i, grubbsG x = |x i - sampleMean x| / sampleStdDev x := by
  have : Nonempty (Fin n) := by
    rcases isEmpty_or_nonempty (Fin n) with he | hne
    · refine absurd ?_ h
      simp [sampleStdDev, sampleVarUnbiased_eq_sum_div]
    · exact hne
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => |x i - sampleMean x|)
  exact ⟨i, by rw [grubbsG_of_ne x h, ← hi]⟩

/-- Grubbs decision procedure: reject the most extreme observation of `x` at the critical value
`gcrit ≥ 0`. The critical value is an explicit nonnegative input (tabulated values assume
normality); a negative `gcrit` never rejects. -/
def grubbsReject {n : ℕ} (x : Fin n → ℝ) (gcrit : ℝ) : Prop :=
  0 ≤ gcrit ∧ gcrit < grubbsG x

/-- Rejection is monotone in the critical value: a smaller nonnegative threshold rejects whenever
a larger one does. -/
lemma grubbsReject_mono {n : ℕ} (x : Fin n → ℝ) (ga gb : ℝ) (hb : 0 ≤ gb) (h : gb ≤ ga)
    (r : grubbsReject x ga) : grubbsReject x gb :=
  ⟨hb, lt_of_le_of_lt h r.2⟩

/-- A sample with zero standard deviation is never rejected by Grubbs' procedure, at any critical
value. -/
lemma not_grubbsReject_of_sd_zero {n : ℕ} (x : Fin n → ℝ) (h : sampleStdDev x = 0)
    (gcrit : ℝ) : ¬ grubbsReject x gcrit := by
  rintro ⟨hg, hlt⟩
  rw [grubbsG_of_sd_zero x h] at hlt
  exact absurd hlt (not_lt.mpr hg)

/-! ## E. Multiplicity adjustment and detection limits -/

/-- Bonferroni-adjusted level `α/m`: each of `m` p-values is compared with `α/m`, meaningful for
`m ≥ 1` (at `m = 0` Lean's division returns `0`). It is the threshold of the canonical procedure
`MultipleTesting.bonferroniRejections` (`mem_bonferroniRejections_iff`), whose family-wise error
control is proved there. -/
noncomputable def bonferroniLevel (α : ℝ) (m : ℕ) : ℝ :=
  α / (m : ℝ)

/-- The Bonferroni level is nonnegative for nonnegative `α`. -/
lemma bonferroniLevel_nonneg (α : ℝ) (m : ℕ) (hα : 0 ≤ α) :
    0 ≤ bonferroniLevel α m := by
  unfold bonferroniLevel
  apply div_nonneg hα
  positivity

/-- The canonical Bonferroni procedure rejects exactly the hypotheses whose p-value is at most
`bonferroniLevel α m`; its family-wise error control is
`MathlibExt.Probability.Statistics.MultipleTesting.measure_bonferroni_familywiseError_le`. -/
lemma mem_bonferroniRejections_iff {m : ℕ} (α : ℝ) (p : Fin m → ℝ) (i : Fin m) :
    i ∈ MathlibExt.Probability.Statistics.MultipleTesting.bonferroniRejections α p ↔
      p i ≤ bonferroniLevel α m := by
  simp [MathlibExt.Probability.Statistics.MultipleTesting.bonferroniRejections, bonferroniLevel]

/-- Detection limit `LOD = 3·s/m` as a stated convention (not a theorem): `k = 3` convention,
`s` the blank standard deviation, `m` the calibration slope, meaningful for `m > 0` (at `m = 0`
Lean's division returns `0`). -/
noncomputable def lodK3 (s m : ℝ) : ℝ :=
  3 * s / m

/-- The `k = 3` detection limit unfolds to its defining formula. -/
lemma lodK3_eq (s m : ℝ) : lodK3 s m = 3 * s / m :=
  rfl

/-- The `k = 3` detection limit is nonnegative for nonnegative blank SD and
positive slope. -/
lemma lodK3_nonneg (s m : ℝ) (hs : 0 ≤ s) (hm : 0 < m) : 0 ≤ lodK3 s m := by
  unfold lodK3
  apply div_nonneg
  · apply mul_nonneg _ hs
    norm_num
  · exact le_of_lt hm

/-- Detection limit `LOD = 3.3·s/m` as a stated convention (not a theorem): `k = 3.3`
convention, meaningful for `m > 0`. Separate from `lodK3`: state which convention is used and
never mix them. -/
noncomputable def lodK33 (s m : ℝ) : ℝ :=
  3.3 * s / m

/-- The `k = 3.3` detection limit unfolds to its defining formula. -/
lemma lodK33_eq (s m : ℝ) : lodK33 s m = 3.3 * s / m :=
  rfl

/-- The `k = 3.3` detection limit is nonnegative for nonnegative blank SD and
positive slope. -/
lemma lodK33_nonneg (s m : ℝ) (hs : 0 ≤ s) (hm : 0 < m) : 0 ≤ lodK33 s m := by
  unfold lodK33
  apply div_nonneg
  · apply mul_nonneg _ hs
    norm_num
  · exact le_of_lt hm

end Chemistry.StatisticalTreatment
