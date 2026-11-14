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
public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.Statistics.NormalTheory
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
the sample standard deviation and facts about constant samples and `n = 1`.

The two-sided t-interval `x̄ ± t s / √n` covers the mean of an i.i.d. normal sample with
probability exactly `1 - α` when `t` is the upper `α/2` point of Student's t law on `n - 1`
degrees of freedom (`tInterval_coverage`, which restates
`ProbabilityTheory.one_sample_t_interval_coverage_eq`).

The pooled variance of two samples is unbiased for their common variance when each sample is
pairwise independent and identically distributed with finite second moment and the two
variances are equal (`integral_pooledVariance`, from
`MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin`). The two-sample t and
variance-ratio F statistics are formulas only: no distribution claim is made for them.

The Dixon Q and Grubbs statistics are computed from the whole sample: Dixon's Q for observation
`j` is the gap to its nearest other observation over the sample range, and Grubbs' G is the
largest absolute deviation from the sample mean over the sample standard deviation. The decision
procedures compare them with caller-supplied critical values, and Dixon's procedure rejects only
an extreme observation. No error-rate claim is made for these procedures, nor for the Bonferroni
adjustment or the `k = 3` and `k = 3.3` detection-limit conventions, which are stated
conventions.

Several formulas divide by a quantity that can vanish; each docstring states the domain on which
the formula is meaningful. Dixon's Q and Grubbs' G are defined to be `0` when the spread is `0`.

## ii. Key results

- `sampleMean_const`, `sampleVarUnbiased_nonneg`, `sampleVarUnbiased_const`,
  `sampleVarUnbiased_fin_one`, `sampleStdDev_const`: constant samples, nonnegativity for
  `2 ≤ n`, and the degenerate value `0` at `n = 1`.
- `tHalfWidth_nonneg`, `mem_tInterval_iff`: the t half-width and the membership duality.
- `tInterval_coverage`: exact coverage `1 - α` of the t-interval for i.i.d. normal samples.
- `pooledVariance_nonneg`, `pooledStdDev_sq`: the pooled variance and standard deviation.
- `integral_pooledVariance`: the pooled variance is unbiased under the equal-variance model.
- `varianceRatioF_nonneg`: the F-ratio shape is nonnegative for nonnegative inputs.
- `dixonQ_of_ne`, `dixonQ_of_no_spread`, `dixonQ_nonneg`, `dixonReject_mono`: Dixon's Q.
- `grubbsG_of_ne`, `grubbsG_of_sd_zero`, `grubbsG_nonneg`, `div_le_grubbsG`,
  `exists_grubbsG_eq`, `grubbsReject_mono`: Grubbs' G is the largest standardized residual.
- `bonferroniLevel_nonneg`, `lodK3_nonneg`, `lodK33_nonneg`: nonnegativity of the stated
  multiplicity and detection-limit conventions.

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
  variance) and `MathlibExt.Probability.Statistics.NormalTheory` (exact t-interval coverage).

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

/-- Student-t pivot `(x̄ - μ) / (s / √n)` of a sample, as a formula, meaningful when `s > 0` and
`n ≥ 1` (otherwise Lean's division returns `0`). -/
noncomputable def tPivot {n : ℕ} (x : Fin n → ℝ) (μ : ℝ) : ℝ :=
  (sampleMean x - μ) / (sampleStdDev x / Real.sqrt (n : ℝ))

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

/-! ## C. Pooled variance and two-sample statistics -/

/-- Pooled variance `((n₁-1)s₁² + (n₂-1)s₂²) / (n₁+n₂-2)` of two samples from their unbiased
sample variances, meaningful for `n₁, n₂ ≥ 2` (then the denominator is positive,
`pooledDenom_ne_zero`). It is unbiased under the equal-variance model
(`integral_pooledVariance`). -/
noncomputable def pooledVariance (n1 n2 : ℕ) (s1sq s2sq : ℝ) : ℝ :=
  (((n1 - 1 : ℕ) : ℝ) * s1sq + ((n2 - 1 : ℕ) : ℝ) * s2sq)
    / ((n1 + n2 - 2 : ℕ) : ℝ)

/-- The pooled denominator is nonzero for `2 ≤ n₁` and `2 ≤ n₂`. -/
lemma pooledDenom_ne_zero (n1 n2 : ℕ) (h1 : 2 ≤ n1) (h2 : 2 ≤ n2) :
    ((n1 + n2 - 2 : ℕ) : ℝ) ≠ 0 := by
  have hpos : 0 < n1 + n2 - 2 := by omega
  have hcast : (0 : ℝ) < ((n1 + n2 - 2 : ℕ) : ℝ) := by exact_mod_cast hpos
  exact ne_of_gt hcast

/-- The pooled variance is nonnegative for nonnegative inputs. -/
lemma pooledVariance_nonneg (n1 n2 : ℕ) (s1sq s2sq : ℝ)
    (h1 : 0 ≤ s1sq) (h2 : 0 ≤ s2sq) : 0 ≤ pooledVariance n1 n2 s1sq s2sq := by
  unfold pooledVariance
  apply div_nonneg
  · apply add_nonneg
    · exact mul_nonneg (by positivity) h1
    · exact mul_nonneg (by positivity) h2
  · positivity

/-- The pooled weights `n₁ - 1` and `n₂ - 1` add up to the denominator `n₁ + n₂ - 2`. -/
private lemma pooled_weights_sum (n1 n2 : ℕ) (h1 : 2 ≤ n1) (h2 : 2 ≤ n2) :
    ((n1 - 1 : ℕ) : ℝ) + ((n2 - 1 : ℕ) : ℝ) = ((n1 + n2 - 2 : ℕ) : ℝ) := by
  have e1 : ((n1 - 1 : ℕ) : ℝ) = (n1 : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n1)]
    norm_num
  have e2 : ((n2 - 1 : ℕ) : ℝ) = (n2 : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n2)]
    norm_num
  have eD : ((n1 + n2 - 2 : ℕ) : ℝ) = (n1 : ℝ) + (n2 : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n1 + n2), Nat.cast_add]
    norm_num
  rw [e1, e2, eD]
  ring

/-- **The pooled variance is unbiased under the equal-variance model.** Let `X i`, `i : Fin n₁`,
and `Y j`, `j : Fin n₂`, with `n₁, n₂ ≥ 2`, be two samples on a probability space. Each sample is
pairwise independent and identically distributed (common laws those of `X i0` and `Y j0`) with
finite second moment, and the two variances are equal: `Var Y j0 = Var X i0`, the
equal-variance model hypothesis. Then the pooled variance of the two unbiased sample variances
is integrable and its expectation is the common variance. No independence between the two
samples is needed: each sample variance is unbiased
(`MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin`), and the pooled variance
is a weighted average of the two. -/
theorem integral_pooledVariance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n1 n2 : ℕ} (h1 : 2 ≤ n1) (h2 : 2 ≤ n2)
    (X : Fin n1 → Ω → ℝ) (Y : Fin n2 → Ω → ℝ) (i0 : Fin n1) (j0 : Fin n2)
    (hXind : Pairwise fun i j => X i ⟂ᵢ[P] X j) (hXid : ∀ i, IdentDistrib (X i) (X i0) P P)
    (hX2 : MemLp (X i0) 2 P)
    (hYind : Pairwise fun i j => Y i ⟂ᵢ[P] Y j) (hYid : ∀ j, IdentDistrib (Y j) (Y j0) P P)
    (hY2 : MemLp (Y j0) 2 P) (hvar : variance (Y j0) P = variance (X i0) P) :
    Integrable (fun ω => pooledVariance n1 n2 (sampleVarUnbiased fun i => X i ω)
      (sampleVarUnbiased fun j => Y j ω)) P ∧
    ∫ ω, pooledVariance n1 n2 (sampleVarUnbiased fun i => X i ω)
      (sampleVarUnbiased fun j => Y j ω) ∂P = variance (X i0) P := by
  obtain ⟨iX, eX⟩ :=
    MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin h1 X i0 hXind hXid hX2
  obtain ⟨iY, eY⟩ :=
    MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin h2 Y j0 hYind hYid hY2
  have hD := pooledDenom_ne_zero n1 n2 h1 h2
  unfold pooledVariance
  refine ⟨((iX.const_mul _).add (iY.const_mul _)).div_const _, ?_⟩
  rw [integral_div, integral_add (iX.const_mul _) (iY.const_mul _), integral_const_mul,
    integral_const_mul, eX, eY, hvar, ← add_mul, pooled_weights_sum n1 n2 h1 h2]
  field_simp

/-- Pooled standard deviation `s_p = √pooledVariance`. -/
noncomputable def pooledStdDev (n1 n2 : ℕ) (s1sq s2sq : ℝ) : ℝ :=
  Real.sqrt (pooledVariance n1 n2 s1sq s2sq)

/-- The squared pooled SD recovers the pooled variance. -/
lemma pooledStdDev_sq (n1 n2 : ℕ) (s1sq s2sq : ℝ)
    (h1 : 0 ≤ s1sq) (h2 : 0 ≤ s2sq) :
    (pooledStdDev n1 n2 s1sq s2sq) ^ 2 = pooledVariance n1 n2 s1sq s2sq := by
  unfold pooledStdDev
  exact Real.sq_sqrt (pooledVariance_nonneg n1 n2 s1sq s2sq h1 h2)

/-- Two-sample t-statistic `(x̄₁ - x̄₂) / (s_p √(1/n₁ + 1/n₂))` built from the pooled SD `sp`,
meaningful for positive group sizes and `sp > 0` (otherwise Lean's division returns `0`). The
Student-t reference distribution assumes i.i.d. normal samples with equal variances; no
distribution or error-rate claim is made here. -/
noncomputable def twoSampleT (xbar1 xbar2 sp : ℝ) (n1 n2 : ℕ) : ℝ :=
  (xbar1 - xbar2) / (sp * Real.sqrt (1 / (n1 : ℝ) + 1 / (n2 : ℝ)))

/-- Variance ratio `F = s₁²/s₂²` for comparing two sample variances (F-test statistic shape),
meaningful for `s₂² > 0` (at `s₂² = 0` Lean's division returns `0`). Tabulated F critical values
assume i.i.d. normal samples with independent groups; this definition carries no error-rate
claim. -/
noncomputable def varianceRatioF (s1sq s2sq : ℝ) : ℝ :=
  s1sq / s2sq

/-- The variance ratio is nonnegative for nonnegative inputs. -/
lemma varianceRatioF_nonneg (s1sq s2sq : ℝ) (h1 : 0 ≤ s1sq) (h2 : 0 ≤ s2sq) :
    0 ≤ varianceRatioF s1sq s2sq := by
  unfold varianceRatioF
  exact div_nonneg h1 h2

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

/-- Dixon decision procedure: reject observation `j` at critical value `qcrit` when it is extreme
and its Q statistic exceeds `qcrit`. The critical value is an explicit input (tabulated values
assume normality). -/
def dixonReject {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (qcrit : ℝ) : Prop :=
  IsExtremeObservation x j ∧ qcrit < dixonQ x j

/-- Rejection is monotone in the critical value: a smaller threshold rejects whenever a larger
one does. -/
lemma dixonReject_mono {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (qa qb : ℝ) (h : qb ≤ qa)
    (r : dixonReject x j qa) : dixonReject x j qb :=
  ⟨r.1, lt_of_le_of_lt h r.2⟩

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

/-- Grubbs decision procedure: reject the most extreme observation of `x` at critical value
`gcrit`. The critical value is an explicit input (tabulated values assume normality). -/
def grubbsReject {n : ℕ} (x : Fin n → ℝ) (gcrit : ℝ) : Prop :=
  gcrit < grubbsG x

/-- Rejection is monotone in the critical value. -/
lemma grubbsReject_mono {n : ℕ} (x : Fin n → ℝ) (ga gb : ℝ) (h : gb ≤ ga)
    (r : grubbsReject x ga) : grubbsReject x gb :=
  lt_of_le_of_lt h r

/-! ## E. Multiplicity adjustment and detection limits -/

/-- Bonferroni-adjusted level `α/m`: the conventional multiplicity adjustment comparing each of
`m` p-values to `α/m`, meaningful for `m ≥ 1` (at `m = 0` Lean's division returns `0`). Stated as
a conventional adjustment procedure; no error-rate claim is proved here. -/
noncomputable def bonferroniLevel (α : ℝ) (m : ℕ) : ℝ :=
  α / (m : ℝ)

/-- The Bonferroni level is nonnegative for nonnegative `α`. -/
lemma bonferroniLevel_nonneg (α : ℝ) (m : ℕ) (hα : 0 ≤ α) :
    0 ≤ bonferroniLevel α m := by
  unfold bonferroniLevel
  apply div_nonneg hα
  positivity

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
