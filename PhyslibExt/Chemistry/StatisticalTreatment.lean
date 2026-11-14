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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Statistical treatment of analytical data

Descriptive statistics, t-intervals, pooled variance, F and t statistics, outlier-test
procedures, and detection-limit conventions for quantitative analysis.

## i. Overview

This module formalizes the standard statistical toolkit of analytical chemistry: the sample
mean and Bessel-corrected sample variance, nominal Student-t confidence intervals, the pooled
variance of two samples with assumed-equal variances, the two-sample t and variance-ratio F
statistic shapes, the Dixon Q and Grubbs outlier procedures, the Bonferroni multiplicity
adjustment, and the `k = 3` / `k = 3.3` detection-limit conventions.

Model boundary. Every definition- and claim-level item is conditional on the sampling model
stated alongside it. All distribution and error-rate claims (nominal coverage, tabulated
critical values, false-rejection rates) require the stated iid-normal / independence
hypotheses; without them the statistics below are bare formulas and ratios with no validity
claim.

Visible deferral. The nominal Student-t coverage claim is VISIBLE DEFERRED:
`studentTCoverageClaim` is a bare `Prop`-valued definition, not asserted, because the pinned
Mathlib supplies no proved Student-t distribution facts (distribution of the pivot,
independence of mean and variance). It is deferred visibly rather than assumed as a hidden
model field. Likewise the LOD (`lodK3`, `lodK33`), Dixon (`dixonQ`, `dixonReject`), Grubbs
(`grubbsG`, `grubbsReject`), and Bonferroni (`bonferroniLevel`) items are stated conventions
and decision procedures, not theorems: no error-rate claim is made for them here.

## ii. Key results

- `sampleMean_const`: the mean of a constant sample is the constant.
- `sampleVariance_nonneg`, `sampleVariance_const`, `sampleVariance_fin_one`: the variance is
  nonnegative for `2 ≤ n`, zero for constant samples, and degenerate (`0`) at `n = 1`.
- `sampleStdDev_const`: constant samples have zero standard deviation.
- `tHalfWidth_nonneg`, `mem_tInterval_iff`: nonnegativity of the t half-width and the
  membership/within-half-width duality (pure algebra).
- `pooledVariance_nonneg`, `pooledVariance_unbiased`: the pooled variance is nonnegative
  and, under additivity/homogeneity of expectation plus unbiasedness of both inputs for a
  common variance, unbiased for that variance.
- `pooledStdDev_sq`: the squared pooled SD recovers the pooled variance.
- `varianceRatioF_nonneg`: the F-ratio shape is nonnegative for nonnegative inputs.
- `dixonQ_of_ne`, `dixonQ_of_no_spread`, `dixonQ_nonneg`, `dixonReject_mono`: Dixon
  unfolding, degeneracy, nonnegativity, and critical-value monotonicity.
- `grubbsG_of_ne`, `grubbsG_of_sd_zero`, `grubbsG_nonneg`, `grubbsReject_mono`: the same
  battery for the Grubbs statistic.
- `bonferroniLevel_nonneg`, `lodK3_nonneg`, `lodK33_nonneg`: nonnegativity of the stated
  multiplicity and detection-limit conventions.

## iii. Table of contents

- A. Sample mean, variance, and standard deviation
- B. t-intervals, the Student-t pivot, and the deferred coverage claim
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
- `Mathlib.Analysis.Real.Sqrt`, `Mathlib.Order.Interval.Set.Basic`, and the Mathlib
  big-operator API for the analytic facts used.

## A. Sample mean, variance, and standard deviation
-/

@[expose] public section

namespace Chemistry.StatisticalTreatment

/-- Sample mean `x̄ = (∑ i, x i) / n` of `n` measurements. -/
noncomputable def sampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) / (n : ℝ)

/-- The mean of a constant sample is the constant. -/
lemma sampleMean_const (n : ℕ) (hn : n ≠ 0) (c : ℝ) (x : Fin n → ℝ)
    (h : ∀ i, x i = c) : sampleMean x = c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsum : (∑ i, x i) = (n : ℝ) * c := by
    have h1 : (∑ i, x i) = Finset.sum Finset.univ (fun _ : Fin n => c) :=
      Finset.sum_congr rfl (fun i _ => h i)
    rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold sampleMean
  rw [hsum]
  field_simp

/-- Unbiased sample variance `s² = ∑ (xᵢ - x̄)² / (n - 1)` (Bessel-corrected).
Needs `2 ≤ n`; at `n = 1` the denominator vanishes
(see `sampleVariance_fin_one`). -/
noncomputable def sampleVariance {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - sampleMean x) ^ 2) / ((n - 1 : ℕ) : ℝ)

/-- Sample variance is nonnegative for `2 ≤ n`. -/
lemma sampleVariance_nonneg (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ) :
    0 ≤ sampleVariance x := by
  unfold sampleVariance
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i _
    positivity
  · have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [h2]
    have h1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith

/-- Constant samples have zero variance. -/
lemma sampleVariance_const (n : ℕ) (hn : n ≠ 0) (c : ℝ) (x : Fin n → ℝ)
    (h : ∀ i, x i = c) : sampleVariance x = 0 := by
  have hmean : sampleMean x = c := sampleMean_const n hn c x h
  have hsum : (∑ i, (x i - sampleMean x) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [h i, hmean]
    norm_num
  unfold sampleVariance
  rw [hsum]
  simp

/-- At `n = 1` the sample variance is degenerate (denominator `1 - 1 = 0`), so
no t-procedure built on it carries a claim. -/
lemma sampleVariance_fin_one (x : Fin 1 → ℝ) : sampleVariance x = 0 := by
  have hden : ((1 - 1 : ℕ) : ℝ) = 0 := by norm_num
  unfold sampleVariance
  rw [hden, div_zero]

/-- Sample standard deviation `s = √s²`. -/
noncomputable def sampleStdDev {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (sampleVariance x)

/-- Constant samples have zero standard deviation. -/
lemma sampleStdDev_const (n : ℕ) (hn : n ≠ 0) (c : ℝ) (x : Fin n → ℝ)
    (h : ∀ i, x i = c) : sampleStdDev x = 0 := by
  unfold sampleStdDev
  rw [sampleVariance_const n hn c x h, Real.sqrt_zero]

/-! ## B. t-intervals, the Student-t pivot, and the deferred coverage claim -/

/-- Half-width `tcrit * s / √n` of a t-interval. -/
noncomputable def tHalfWidth (s : ℝ) (n : ℕ) (tcrit : ℝ) : ℝ :=
  tcrit * s / Real.sqrt (n : ℝ)

/-- The half-width is nonnegative for nonnegative critical value and scale. -/
lemma tHalfWidth_nonneg (s : ℝ) (n : ℕ) (tcrit : ℝ) (ht : 0 ≤ tcrit)
    (hs : 0 ≤ s) : 0 ≤ tHalfWidth s n tcrit := by
  unfold tHalfWidth
  exact div_nonneg (mul_nonneg ht hs) (Real.sqrt_nonneg _)

/-- Nominal t-interval `x̄ ± tcrit * s / √n` as a set. This is the interval
formula; nominal coverage is the separately deferred claim
(`studentTCoverageClaim`), not asserted here. -/
def tInterval (xbar s : ℝ) (n : ℕ) (tcrit : ℝ) : Set ℝ :=
  Set.Icc (xbar - tHalfWidth s n tcrit) (xbar + tHalfWidth s n tcrit)

/-- A value lies in the t-interval iff it is within one half-width of the mean.
This duality is pure algebra; nominal coverage is the deferred claim below. -/
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

/-- Student-t pivot `(x̄ - μ) / (s / √n)` as a formula. Its Student-t
distribution (and hence nominal coverage) is the deferred claim; see
`studentTCoverageClaim`. -/
noncomputable def tPivot {n : ℕ} (x : Fin n → ℝ) (μ : ℝ) : ℝ :=
  (sampleMean x - μ) / (sampleStdDev x / Real.sqrt (n : ℝ))

/-- **DEFERRED: nominal Student-t coverage (MC target, visible deferral).**
The intended claim: under iid normal sampling with `2 ≤ n` and positive
variance, with `tcrit` the two-sided Student-t critical value at level `α`,
the t-interval covers the true mean with probability `1 - α`. Stated here as a
bare proposition -- NOT asserted -- because the pinned Mathlib supplies no
proved Student-t distribution facts (distribution of the pivot, independence of
mean and variance). Per the contract this is deferred visibly instead of being
assumed as a hidden model field. -/
def studentTCoverageClaim (P : Set ℝ → ℝ) (xbar s : ℝ) (n : ℕ) (tcrit α : ℝ) :
    Prop :=
  P (tInterval xbar s n tcrit) = 1 - α

/-! ## C. Pooled variance and two-sample statistics -/

/-- Pooled variance `((n₁-1)s₁² + (n₂-1)s₂²) / (n₁+n₂-2)` for two samples with
assumed-equal variances. Takes the two unbiased sample variances as arguments. -/
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

/-- **Pooled variance is the unbiased estimator (MC target).** For any
expectation operator `E` with additivity (`h_add`) and homogeneity (`h_hom`,
constants factor out on the left), if both sample variances are unbiased for a
common variance `σ2` (the equal-variance model hypothesis, MOD), then the
pooled variance is unbiased for `σ2`. -/
lemma pooledVariance_unbiased (E : ℝ → ℝ)
    (h_add : ∀ a b : ℝ, E (a + b) = E a + E b)
    (h_hom : ∀ (c v : ℝ), E (c * v) = c * E v)
    (n1 n2 : ℕ) (h1 : 2 ≤ n1) (h2 : 2 ≤ n2)
    (s1sq s2sq σ2 : ℝ) (u1 : E s1sq = σ2) (u2 : E s2sq = σ2) :
    E (pooledVariance n1 n2 s1sq s2sq) = σ2 := by
  have hden : ((n1 + n2 - 2 : ℕ) : ℝ) ≠ 0 :=
    pooledDenom_ne_zero n1 n2 h1 h2
  have h_hom' : ∀ (v c : ℝ), E (v * c) = E v * c := fun v c => by
    rw [mul_comm v c, h_hom, mul_comm c (E v)]
  have hsplit : pooledVariance n1 n2 s1sq s2sq
      = ((((n1 - 1 : ℕ) : ℝ) * s1sq + ((n2 - 1 : ℕ) : ℝ) * s2sq))
        * (((n1 + n2 - 2 : ℕ) : ℝ))⁻¹ := by
    unfold pooledVariance
    rw [div_eq_mul_inv]
  rw [hsplit, h_hom', h_add, h_hom, h_hom, u1, u2]
  have hsum : ((n1 - 1 : ℕ) : ℝ) + ((n2 - 1 : ℕ) : ℝ)
      = ((n1 + n2 - 2 : ℕ) : ℝ) := by
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
  have hcancel : ((n1 + n2 - 2 : ℕ) : ℝ) * (((n1 + n2 - 2 : ℕ) : ℝ))⁻¹ = 1 :=
    mul_inv_cancel₀ hden
  have hfactor : ((((n1 - 1 : ℕ) : ℝ)) * σ2 + (((n2 - 1 : ℕ) : ℝ)) * σ2)
      * (((n1 + n2 - 2 : ℕ) : ℝ))⁻¹
      = ((((n1 - 1 : ℕ) : ℝ) + ((n2 - 1 : ℕ) : ℝ))
        * (((n1 + n2 - 2 : ℕ) : ℝ))⁻¹) * σ2 := by
    ring
  rw [hfactor, hsum, hcancel, one_mul]

/-- Pooled standard deviation `s_p = √pooledVariance`. -/
noncomputable def pooledStdDev (n1 n2 : ℕ) (s1sq s2sq : ℝ) : ℝ :=
  Real.sqrt (pooledVariance n1 n2 s1sq s2sq)

/-- The squared pooled SD recovers the pooled variance. -/
lemma pooledStdDev_sq (n1 n2 : ℕ) (s1sq s2sq : ℝ)
    (h1 : 0 ≤ s1sq) (h2 : 0 ≤ s2sq) :
    (pooledStdDev n1 n2 s1sq s2sq) ^ 2 = pooledVariance n1 n2 s1sq s2sq := by
  unfold pooledStdDev
  exact Real.sq_sqrt (pooledVariance_nonneg n1 n2 s1sq s2sq h1 h2)

/-- Two-sample t-statistic `(x̄₁ - x̄₂) / (s_p √(1/n₁ + 1/n₂))` built from the
pooled SD `sp`, for positive group sizes. The Student-t reference distribution
assumes iid normal samples with equal variances (MOD); no distribution or
error-rate claim is made here. -/
noncomputable def twoSampleT (xbar1 xbar2 sp : ℝ) (n1 n2 : ℕ) : ℝ :=
  (xbar1 - xbar2) / (sp * Real.sqrt (1 / (n1 : ℝ) + 1 / (n2 : ℝ)))

/-- Variance ratio `F = s₁²/s₂²` for comparing two sample variances (F-test
statistic shape). Tabulated F critical values assume iid normal samples with
independent groups (MOD); this definition alone carries no error-rate claim. -/
noncomputable def varianceRatioF (s1sq s2sq : ℝ) : ℝ :=
  s1sq / s2sq

/-- The variance ratio is nonnegative for nonnegative inputs. -/
lemma varianceRatioF_nonneg (s1sq s2sq : ℝ) (h1 : 0 ≤ s1sq) (h2 : 0 ≤ s2sq) :
    0 ≤ varianceRatioF s1sq s2sq := by
  unfold varianceRatioF
  exact div_nonneg h1 h2

/-! ## D. Outlier procedures: Dixon Q and Grubbs -/

/-- Dixon Q statistic `|suspect - nearest| / (max - min)` from the ordered
statistics supplied by the caller (`suspect` value under test, its `nearest`
neighbour, and the sample extremes `mn`/`mx`). Returns `0` when `mx = mn`
(no spread, hence no rejection). For a single pre-specified suspect;
tabulated critical values -- and any error-rate meaning of the comparison --
assume iid normal sampling (MOD). Without that hypothesis this is a bare ratio
with no validity claim. -/
noncomputable def dixonQ (suspect nearest mn mx : ℝ) : ℝ :=
  if mx = mn then 0 else |suspect - nearest| / (mx - mn)

/-- Unfolding of `dixonQ` away from the degenerate case. -/
lemma dixonQ_of_ne (suspect nearest mn mx : ℝ) (h : mx ≠ mn) :
    dixonQ suspect nearest mn mx = |suspect - nearest| / (mx - mn) := by
  unfold dixonQ
  rw [ite_eq_right h]

/-- With no spread the Dixon statistic is `0`. -/
lemma dixonQ_of_no_spread (suspect nearest mn mx : ℝ) (h : mx = mn) :
    dixonQ suspect nearest mn mx = 0 := by
  unfold dixonQ
  rw [ite_eq_left h]

/-- Dixon Q is nonnegative when the extremes are ordered. -/
lemma dixonQ_nonneg (suspect nearest mn mx : ℝ) (h : mn ≤ mx) :
    0 ≤ dixonQ suspect nearest mn mx := by
  by_cases h0 : mx = mn
  · rw [dixonQ_of_no_spread suspect nearest mn mx h0]
  · rw [dixonQ_of_ne suspect nearest mn mx h0]
    exact div_nonneg (abs_nonneg _) (by linarith)

/-- Dixon decision procedure: reject the suspect at critical value `qcrit`.
The critical value is an explicit input (tabulated values assume normality). -/
def dixonReject (Q qcrit : ℝ) : Prop :=
  qcrit < Q

/-- Rejection is monotone in the critical value: a stricter (smaller) threshold
rejects whenever a laxer one does. -/
lemma dixonReject_mono (Q qa qb : ℝ) (h : qb ≤ qa) (r : dixonReject Q qa) :
    dixonReject Q qb := by
  unfold dixonReject at *
  exact lt_of_le_of_lt h r

/-- Grubbs statistic `|xj - xbar| / s` for the value `xj` given the sample mean
`xbar` and sample SD `s`. Returns `0` when `s = 0` (no spread, hence no
rejection). For a single pre-specified suspect; as with Dixon's Q, tabulated
critical values assume iid normal sampling (MOD), and without it this is a
bare ratio with no validity claim. -/
noncomputable def grubbsG (xj xbar s : ℝ) : ℝ :=
  if s = 0 then 0 else |xj - xbar| / s

/-- Unfolding of `grubbsG` away from the degenerate case. -/
lemma grubbsG_of_ne (xj xbar s : ℝ) (h : s ≠ 0) :
    grubbsG xj xbar s = |xj - xbar| / s := by
  unfold grubbsG
  rw [ite_eq_right h]

/-- With zero spread the Grubbs statistic is `0`: degenerate input produces no
rejection at any positive critical value, hence no error-rate-backed claim. -/
lemma grubbsG_of_sd_zero (xj xbar : ℝ) : grubbsG xj xbar 0 = 0 := by
  unfold grubbsG
  rw [ite_eq_left rfl]

/-- The Grubbs statistic is nonnegative for nonnegative scale. -/
lemma grubbsG_nonneg (xj xbar s : ℝ) (hs : 0 ≤ s) : 0 ≤ grubbsG xj xbar s := by
  by_cases h0 : s = 0
  · rw [h0, grubbsG_of_sd_zero]
  · rw [grubbsG_of_ne xj xbar s h0]
    exact div_nonneg (abs_nonneg _) hs

/-- Grubbs decision procedure: reject the suspect at critical value `gcrit`.
The critical value is an explicit input (tabulated values assume normality). -/
def grubbsReject (G gcrit : ℝ) : Prop :=
  gcrit < G

/-- Rejection is monotone in the critical value. -/
lemma grubbsReject_mono (G ga gb : ℝ) (h : gb ≤ ga) (r : grubbsReject G ga) :
    grubbsReject G gb := by
  unfold grubbsReject at *
  exact lt_of_le_of_lt h r

/-! ## E. Multiplicity adjustment and detection limits -/

/-- Bonferroni-adjusted level `α/m`: the conventional multiplicity adjustment
comparing each of `m` p-values to `α/m` (multiple-testing boundary). Stated as
a conventional adjustment procedure, not proved here. -/
noncomputable def bonferroniLevel (α : ℝ) (m : ℕ) : ℝ :=
  α / (m : ℝ)

/-- The Bonferroni level is nonnegative for nonnegative `α`. -/
lemma bonferroniLevel_nonneg (α : ℝ) (m : ℕ) (hα : 0 ≤ α) :
    0 ≤ bonferroniLevel α m := by
  unfold bonferroniLevel
  apply div_nonneg hα
  positivity

/-- Detection limit `LOD = 3·s/m` as a stated convention (NOT a theorem):
`k = 3` convention, `s` blank standard deviation, `m` calibration slope. -/
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

/-- Detection limit `LOD = 3.3·s/m` as a stated convention (NOT a theorem):
`k = 3.3` convention. Separate from `lodK3`: state which convention is used
and never mix them. -/
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
