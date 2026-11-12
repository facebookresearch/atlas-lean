/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ExponentialMoments
public import MathlibExt.Probability.Distributions.Weibull
public import MathlibExt.Probability.Statistics.LinearModel.Inference
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.StrongLaw

/-!
# Continuous distributions, sampling identities and sampling limits

Gaussian, exponential and Maxwell moments, sample-mean identities and limits, and Student-t,
Weibull and JMAK statements under explicit hypotheses.

## i. Overview

The file imports Mathlib and ATLAS. The Gaussian statements reuse `ProbabilityTheory.gaussianReal`
and the exponential ones `ProbabilityTheory.expMeasure`. The Gaussian normalization
`ProbabilityTheory.integral_gaussianPDFReal_eq_one` (for `v ≠ 0`), the Gaussian mean
`ProbabilityTheory.integral_id_gaussianReal` and the exponential normalization
`ProbabilityTheory.lintegral_exponentialPDF_eq_one` (for `0 < r`) are Mathlib declarations, used
as they are. This file adds the central second moment of `gaussianReal μ v`. The exponential mean
is used directly as ATLAS's `ProbabilityTheory.integral_id_expMeasure` (`r⁻¹`, for `0 < r`); this
file adds no wrapper for it.

For identically distributed `X : ℕ → Ω → ℝ` the sample mean `sampleMean X n` has expectation
`E[X 0]` (`integral_sampleMean`), and for pairwise independent `X i` with a finite second moment
it has variance `Var[X 0] / n` (`variance_sampleMean`), for `n ≠ 0`. These are finite-sample
identities. Almost-sure convergence of the sample mean to `E[X 0]` is the strong law of large
numbers, Mathlib's `ProbabilityTheory.strong_law_ae_real`, specialized in `ae_tendsto_sampleMean`.
A finite-sample expectation identity is not almost-sure or asymptotic consistency, and the two
are separate theorems.

`StudentTPivotLaw` bundles the classical prerequisites of the t-interval (`2 ≤ n`,
`0 < σ`, independent `N(μ, σ ^ 2)` observations). The pivot law is a theorem of this file,
`StudentTPivotLaw.hasLaw_pivot`: the pivot `√n (x̄ - μ) / s` has law
`ProbabilityTheory.studentTMeasure (n - 1)`, derived from the observation fields via
`ProbabilityTheory.map_tStatistic_pi_gaussianReal` (the one-sample `t` law) transported along
`iIndepFun.hasLaw_pi`. Coverage of the interval `x̄ ± q s / √n` is then unconditional on the
prerequisites; the observation fields are also used to show that `s > 0` almost surely.

`weibullSurvival k lam` is the survival function of ATLAS's Weibull law
`ProbabilityTheory.weibullMeasure k lam` (`weibullSurvival_eq_weibullMeasure_real_Ioi`): a real
survival function whose cumulative hazard `(x / lam) ^ k` is the power-law form
(`neg_log_weibullMeasure_real_Ioi`). Independence of links, or of volume elements, is a separate
hypothesis on the joint survival: the system survival is the product of the component survivals.
Neither hypothesis is derived from the other. Independence alone gives the survival `S ^ n` of a
chain of `n` links with common survival `S`; with the power-law hazard as well, the chain is again
of Weibull form (`weibullSurvival_rpow`).

`voidProbability kappa volume = exp (-kappa * volume)` is a stipulated JMAK void-probability
model, not derived from a point process. Constructing a continuum Poisson point process and
deriving the void law from it is a separately scoped extension that this file does not contain
and does not claim. The Avrami form `1 - exp (-K * t ^ n)` follows by substituting the extended
volume.

`maxwellSpeedPDF a` is the Maxwell speed density with scale `a` on `(0, ∞)`. Its normalization
and second moment follow from Mathlib's Gamma-function integrals.

ATLAS has a related declaration that this file does not import:
`MathlibExt.Probability.variance_sample_mean_of_iid`, which assumes mutual independence where
`variance_sampleMean` assumes pairwise independence.

## ii. Key results

- `integral_sub_sq_gaussianReal` : the Gaussian central second moment.
- `integral_sampleMean`, `variance_sampleMean` : finite-sample expectation and variance of the
  sample mean.
- `StudentTPivotLaw.hasLaw_pivot` : the pivot has Student-t law `studentTMeasure (n - 1)`.
- `StudentTPivotLaw.measure_mem_studentTInterval`,
  `StudentTPivotLaw.measureReal_mem_studentTInterval` : t-interval coverage.
- `ae_tendsto_sampleMean` : the strong law of large numbers for the sample mean.
- `weibullSurvival_zero`, `antitone_weibullSurvival`, `tendsto_weibullSurvival_atTop`,
  `neg_log_weibullSurvival` : the Weibull survival function and its hazard.
- `weibullSurvival_eq_weibullMeasure_real_Ioi`, `measureReal_gt_eq_weibullSurvival` :
  the bridge to the canonical Weibull law `weibullMeasure`.
- `weakestLink_survival_eq_pow`, `measureReal_forall_lt_eq_prod`, `sizeScaling_survival_eq_rpow`,
  `weibullSurvival_rpow` : conditional weakest-link and size scaling.
- `voidProbability_zero`, `antitone_voidProbability`, `tendsto_voidProbability_atTop`,
  `one_sub_voidProbability_mem_Icc`, `one_sub_voidProbability_eq_avrami` : the JMAK model.
- `integral_maxwellSpeedPDF`, `integral_sq_mul_maxwellSpeedPDF` : Maxwell normalization and
  second moment `3 a ^ 2`.

## iii. Table of contents

- A. Gaussian and exponential laws
- B. Sample mean and the Student-t pivot
- C. Strong law of large numbers
- D. Weibull survival and weakest-link scaling
- E. JMAK void probability
- F. Maxwell speed density

## iv. References

- JCGM 100:2008, *Evaluation of measurement data — Guide to the expression of uncertainty in
  measurement* (GUM): measurement-uncertainty context. The sampling statements here are
  mathematics, not measurements.
- Student, *The probable error of a mean*, Biometrika 6 (1908), 1–25.
- W. Weibull, *A statistical distribution function of wide applicability*, J. Appl. Mech. 18
  (1951), 293–297.
- M. Avrami, *Kinetics of phase change. I. General theory*, J. Chem. Phys. 7 (1939), 1103–1112.
- J. C. Maxwell, *Illustrations of the dynamical theory of gases*, Philos. Mag. 19 (1860), 19–32.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal

namespace MathlibExt.Probability.ContinuousDistributions

/-! ## A. Gaussian and exponential laws -/

/-- **Gaussian central second moment**: `∫ (x - μ) ^ 2 ∂N(μ, v) = v`. Proved from Mathlib's
variance of the Gaussian, `ProbabilityTheory.variance_id_gaussianReal`, unfolded by
`ProbabilityTheory.variance_eq_integral`; no moment-generating-function or
characteristic-function differentiation is used. It holds for every `v : ℝ≥0`, including the
degenerate `v = 0`, where `gaussianReal μ 0` is the Dirac mass at `μ`. -/
lemma integral_sub_sq_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    ∫ x, (x - μ) ^ 2 ∂gaussianReal μ v = v := by
  have h := variance_eq_integral (X := id) (μ := gaussianReal μ v) measurable_id.aemeasurable
  rw [variance_id_gaussianReal] at h
  simpa [integral_id_gaussianReal] using h.symm

/-! ## B. Sample mean and the Student-t pivot -/

/-- The sample mean `(∑ i ∈ range n, X i ω) / n` of the first `n` terms of `X : ℕ → Ω → ℝ`, in
the form used by Mathlib's strong law `ProbabilityTheory.strong_law_ae_real`. For `n = 0` it is
`0` (division by zero); the lemmas below assume `n ≠ 0`. -/
noncomputable def sampleMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / n

/-- **Unbiasedness of the sample mean**: if `X 0` is integrable and every `X i` has the law of
`X 0`, then `E[x̄ₙ] = E[X 0]` for `n ≠ 0`. This finite-sample identity uses linearity of the
integral and no independence. It is not almost-sure or asymptotic consistency, which is the
separate theorem `ae_tendsto_sampleMean`. -/
lemma integral_sampleMean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hint : Integrable (X 0) P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {n : ℕ}
    (hn : n ≠ 0) :
    ∫ ω, sampleMean X n ω ∂P = ∫ ω, X 0 ω ∂P := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [sampleMean]
  rw [integral_div, integral_finsetSum _ fun i _ => (hident i).integrable_iff.mpr hint,
    Finset.sum_congr rfl fun i _ => (hident i).integral_eq, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  field_simp

/-- **Variance of the sample mean**: if `X 0` has a finite second moment and the `X i` are
pairwise independent with the law of `X 0`, then `Var[x̄ₙ] = Var[X 0] / n` for `n ≠ 0`. The proof
uses Mathlib's variance of a sum of independent variables,
`ProbabilityTheory.IndepFun.variance_sum`. -/
lemma variance_sampleMean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (h2 : MemLp (X 0) 2 P) (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {n : ℕ} (hn : n ≠ 0) :
    Var[sampleMean X n; P] = Var[X 0; P] / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfun : sampleMean X n = fun ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i) ω := by
    funext ω
    rw [sampleMean, Finset.sum_apply, div_eq_inv_mul]
  rw [hfun, variance_const_mul,
    IndepFun.variance_sum (fun i _ => (hident i).memLp_iff.mpr h2) fun i _ j _ hij => hindep hij,
    Finset.sum_congr rfl fun i _ => (hident i).variance_eq, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  field_simp

/-- The unbiased sample variance `(∑ i ∈ range n, (X i ω - x̄ₙ) ^ 2) / (n - 1)` of the first `n`
terms. For `n = 1` the divisor is `0` and the value is `0`. -/
noncomputable def sampleVariance {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, (X i ω - sampleMean X n ω) ^ 2) / ((n : ℝ) - 1)

/-- The sample standard deviation `sₙ = √(sampleVariance X n ω)`. -/
noncomputable def sampleStdDev {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  √(sampleVariance X n ω)

/-- The Student-t pivot `√n (x̄ₙ - μ) / sₙ` for the mean `μ`. Where `sₙ = 0` it is `0`, by
Lean's convention for division by zero; under `StudentTPivotLaw` this happens only on a null set
(`StudentTPivotLaw.ae_sampleStdDev_pos`). -/
noncomputable def studentTPivot {Ω : Type*} (X : ℕ → Ω → ℝ) (μ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  √n * (sampleMean X n ω - μ) / sampleStdDev X n ω

/-- The interval `[x̄ₙ - q sₙ / √n, x̄ₙ + q sₙ / √n]` computed from the first `n` observations.
With `q = t_{n-1, 1-α/2}` it is the usual Student-t interval for the mean. It is a set computed
from data and carries no coverage claim. -/
def studentTInterval {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (q : ℝ) (ω : Ω) : Set ℝ :=
  Icc (sampleMean X n ω - q * sampleStdDev X n ω / √n)
    (sampleMean X n ω + q * sampleStdDev X n ω / √n)

/-- **Student-t pivot prerequisites**, as an explicit hypothesis bundle for a sample
`X 0, …, X (n - 1)` under `P`: `2 ≤ n`, `0 < σ`, the observations are independent with law
`N(μ, σ ^ 2)`. The pivot law is not a field: it is the theorem
`StudentTPivotLaw.hasLaw_pivot` below. -/
structure StudentTPivotLaw {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (μ σ : ℝ) (n : ℕ)
    (P : Measure Ω) : Prop where
  /-- At least two observations. -/
  two_le : 2 ≤ n
  /-- A positive standard deviation. -/
  sigma_pos : 0 < σ
  /-- The observations `X 0, …, X (n - 1)` are independent. -/
  indep : iIndepFun (fun i : Fin n => X i) P
  /-- Each observation has law `N(μ, σ ^ 2)`. -/
  hasLaw_sample : ∀ i < n, HasLaw (X i) (gaussianReal μ (σ ^ 2).toNNReal) P

/-- **The pivot has Student's `t` law**: under `StudentTPivotLaw` the pivot
`√n (x̄ₙ - μ) / sₙ` has law `studentTMeasure (n - 1)`. The tuple
`(X 0, …, X (n - 1))` has law `Measure.pi (fun _ => gaussianReal μ (σ ^ 2).toNNReal)` by
`iIndepFun.hasLaw_pi`; composing with the one-sample `t` statistic of
`ProbabilityTheory.map_tStatistic_pi_gaussianReal` gives the pivot law, since the pivot is
that statistic of the tuple (range sums are `Fin n` sums). -/
theorem StudentTPivotLaw.hasLaw_pivot {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ}
    {μ σ : ℝ} {n : ℕ} {P : Measure Ω} (h : StudentTPivotLaw X μ σ n P) :
    HasLaw (studentTPivot X μ n) (studentTMeasure (n - 1)) P := by
  have hv : (σ ^ 2).toNNReal ≠ 0 :=
    (Real.toNNReal_pos.mpr (pow_pos h.sigma_pos 2)).ne'
  have htuple : HasLaw (fun ω (i : Fin n) => X (i : ℕ) ω)
      (Measure.pi fun _ : Fin n => gaussianReal μ (σ ^ 2).toNNReal) P :=
    h.indep.hasLaw_pi fun (i : Fin n) => h.hasLaw_sample (i : ℕ) i.2
  have hT : HasLaw (fun x : Fin n → ℝ =>
        √n * ((∑ i, x i) / n - μ) /
          √((∑ i, (x i - (∑ j, x j) / n) ^ 2) / ((n : ℝ) - 1)))
      (studentTMeasure (n - 1))
      (Measure.pi fun _ : Fin n => gaussianReal μ (σ ^ 2).toNNReal) :=
    ⟨by fun_prop, map_tStatistic_pi_gaussianReal h.two_le μ hv⟩
  have hpivot : studentTPivot X μ n = fun ω =>
      √n * ((∑ i : Fin n, X (i : ℕ) ω) / n - μ) /
        √((∑ i : Fin n, (X (i : ℕ) ω - (∑ j : Fin n, X (j : ℕ) ω) / n) ^ 2) /
          ((n : ℝ) - 1)) := by
    funext ω
    simp only [studentTPivot, sampleMean, sampleStdDev, sampleVariance]
    rw [Fin.sum_univ_eq_sum_range (fun i => X i ω) n,
      Fin.sum_univ_eq_sum_range
        (fun i => (X i ω - (∑ j ∈ Finset.range n, X j ω) / (n : ℝ)) ^ 2) n]
  rw [hpivot]
  exact hT.comp htuple

/-- If the sample standard deviation of at least two observations is not positive, then the
first two observations are equal. -/
private lemma eq_of_not_sampleStdDev_pos {Ω : Type*} {X : ℕ → Ω → ℝ} {n : ℕ} (hn : 2 ≤ n)
    {ω : Ω} (hs : ¬0 < sampleStdDev X n ω) : X 0 ω = X 1 ω := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnonneg : ∀ i ∈ Finset.range n, 0 ≤ (X i ω - sampleMean X n ω) ^ 2 :=
    fun i _ => sq_nonneg _
  have hsum : ∑ i ∈ Finset.range n, (X i ω - sampleMean X n ω) ^ 2 = 0 := by
    rw [sampleStdDev, sqrt_pos, not_lt, sampleVariance, div_le_iff₀ hn1, zero_mul] at hs
    exact le_antisymm hs (Finset.sum_nonneg hnonneg)
  rw [Finset.sum_eq_zero_iff_of_nonneg hnonneg] at hsum
  have h0 := hsum 0 (Finset.mem_range.2 (by omega))
  have h1 := hsum 1 (Finset.mem_range.2 (by omega))
  rw [sq_eq_zero_iff, sub_eq_zero] at h0 h1
  rw [h0, h1]

/-- Under `StudentTPivotLaw` the sample standard deviation is almost surely positive. If
`sₙ = 0` then `X 0 = X 1`, and that event is null because `X 0` and `X 1` are independent and
`N(μ, σ ^ 2)` has no atoms for `σ > 0`. This uses the independence and Gaussian fields, not the
pivot law. -/
lemma StudentTPivotLaw.ae_sampleStdDev_pos {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ}
    {μ σ : ℝ} {n : ℕ} {P : Measure Ω}
    (h : StudentTPivotLaw X μ σ n P) : ∀ᵐ ω ∂P, 0 < sampleStdDev X n ω := by
  have h0 : 0 < n := by have := h.two_le; omega
  have h1 : 1 < n := h.two_le
  have hv : (σ ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.mpr (pow_pos h.sigma_pos 2)).ne'
  have hX0 := h.hasLaw_sample 0 h0
  have hX1 := h.hasLaw_sample 1 h1
  have := hX0.isProbabilityMeasure
  have hind : IndepFun (X 0) (X 1) P :=
    h.indep.indepFun (i := ⟨0, h0⟩) (j := ⟨1, h1⟩) (by simp [Fin.ext_iff])
  have hdiag : P {ω | X 0 ω = X 1 ω} = 0 := by
    have hdiagset : {z : ℝ × ℝ | z.1 = z.2} = diagonal ℝ := rfl
    rw [(hind.hasLaw_prod hX0 hX1).measure_eq (p := fun z : ℝ × ℝ => z.1 = z.2)
      measurableSet_diagonal, hdiagset, Measure.prod_apply measurableSet_diagonal]
    have hpt : ∀ x : ℝ, gaussianReal μ (σ ^ 2).toNNReal (Prod.mk x ⁻¹' diagonal ℝ) = 0 := by
      intro x
      have hx : Prod.mk x ⁻¹' diagonal ℝ = {x} := by
        ext y
        simp [eq_comm]
      rw [hx]
      exact gaussianReal_absolutelyContinuous μ hv Real.volume_singleton
    simp [hpt]
  rw [ae_iff]
  exact measure_mono_null (fun ω hω => eq_of_not_sampleStdDev_pos h.two_le hω) hdiag

/-- **Coverage of the t-interval**: under `StudentTPivotLaw`, the interval
`x̄ₙ ± q sₙ / √n` contains `μ` with probability `studentTMeasure (n - 1) [-q, q]`, for every
`q`. -/
lemma StudentTPivotLaw.measure_mem_studentTInterval {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} {μ σ : ℝ} {n : ℕ} {P : Measure Ω}
    (h : StudentTPivotLaw X μ σ n P) (q : ℝ) :
    P {ω | μ ∈ studentTInterval X n q ω} = studentTMeasure (n - 1) (Icc (-q) q) := by
  have hn : 0 < √(n : ℝ) := sqrt_pos.mpr (by have := h.two_le; positivity)
  have hset : {ω | μ ∈ studentTInterval X n q ω} =ᵐ[P] studentTPivot X μ n ⁻¹' Icc (-q) q := by
    refine Eventually.set_eq ?_
    filter_upwards [h.ae_sampleStdDev_pos] with ω hs
    simp only [mem_preimage, studentTInterval, studentTPivot, mem_Icc, le_div_iff₀ hs,
      div_le_iff₀ hs]
    have key : q * sampleStdDev X n ω / √n * √n = q * sampleStdDev X n ω :=
      div_mul_cancel₀ _ hn.ne'
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rw [measure_congr hset, ← h.hasLaw_pivot.map_eq,
    Measure.map_apply_of_aemeasurable h.hasLaw_pivot.aemeasurable measurableSet_Icc]

/-- **Exact nominal coverage `1 - α`**: if moreover `0 ≤ q` and the Student-t law
`studentTMeasure (n - 1)` gives mass `α / 2` to each of `(-∞, -q)` and `(q, ∞)`, then the interval
`x̄ₙ ± q sₙ / √n` contains `μ` with probability exactly `1 - α`. For the Student-t law with
`n - 1` degrees of freedom the tail conditions say that `q = t_{n-1, 1-α/2}`, by the definition of
the quantile and symmetry. The quantile enters only through these measure statements; no
t-distribution CDF is defined. -/
lemma StudentTPivotLaw.measureReal_mem_studentTInterval {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} {μ σ : ℝ} {n : ℕ} {P : Measure Ω}
    (h : StudentTPivotLaw X μ σ n P) {α q : ℝ} (hq : 0 ≤ q)
    (hlower : (studentTMeasure (n - 1)).real (Iio (-q)) = α / 2)
    (hupper : (studentTMeasure (n - 1)).real (Ioi q) = α / 2) :
    P.real {ω | μ ∈ studentTInterval X n q ω} = 1 - α := by
  have h0 : 0 < n := by have := h.two_le; omega
  have := (h.hasLaw_sample 0 h0).isProbabilityMeasure
  have hn1 : 0 < n - 1 := by have := h.two_le; omega
  have hν : IsProbabilityMeasure (studentTMeasure (n - 1)) :=
    isProbabilityMeasure_studentTMeasure hn1
  have hIic : (studentTMeasure (n - 1)).real (Iic q) =
      (studentTMeasure (n - 1)).real (Iio (-q)) + (studentTMeasure (n - 1)).real (Icc (-q) q) := by
    rw [← Iio_union_Icc_eq_Iic (by linarith : -q ≤ q), measureReal_union _ measurableSet_Icc]
    exact disjoint_left.2 fun x hx hx' => (not_le.2 hx) hx'.1
  have huniv : (studentTMeasure (n - 1)).real univ =
      (studentTMeasure (n - 1)).real (Iic q) + (studentTMeasure (n - 1)).real (Ioi q) := by
    rw [← Iic_union_Ioi (a := q), measureReal_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi]
  rw [measureReal_def, h.measure_mem_studentTInterval q, ← measureReal_def]
  rw [probReal_univ] at huniv
  linarith

/-! ## C. Strong law of large numbers -/

/-- **Strong law of large numbers** for the sample mean: if `X 0` is integrable and the `X i` are
pairwise independent with the law of `X 0`, then `x̄ₙ → E[X 0]` almost surely. This is Mathlib's
`ProbabilityTheory.strong_law_ae_real`, with exactly its hypotheses: pairwise independence
suffices, and no normalization of `P` is assumed. A finite-sample expectation identity
(`integral_sampleMean`) is not almost-sure or asymptotic consistency; the two are separate
theorems. -/
theorem ae_tendsto_sampleMean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hint : Integrable (X 0) P) (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => sampleMean X n ω) atTop (𝓝 (∫ ω, X 0 ω ∂P)) :=
  strong_law_ae_real X hint hindep hident

/-! ## D. Weibull survival and weakest-link scaling -/

/-- The Weibull survival function with shape `k` and scale `lam`: `1` for `x < 0` and
`exp (-(x / lam) ^ k)` for `0 ≤ x`, intended for `0 < k` and `0 < lam`. Its cumulative hazard
`(x / lam) ^ k` (`neg_log_weibullSurvival`) is the power-law form. For `0 < k` and `0 < lam` it is
the survival function `x ↦ P(X > x)` of ATLAS's Weibull law `ProbabilityTheory.weibullMeasure k lam`
(`weibullSurvival_eq_weibullMeasure_real_Ioi`). -/
noncomputable def weibullSurvival (k lam : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 1 else Real.exp (-(x / lam) ^ k)

/-- Below `0` the survival function is `1`. -/
lemma weibullSurvival_of_neg {k lam x : ℝ} (hx : x < 0) : weibullSurvival k lam x = 1 :=
  ite_eq_left hx

/-- On `[0, ∞)` the survival function is `exp (-(x / lam) ^ k)`. -/
lemma weibullSurvival_of_nonneg {k lam x : ℝ} (hx : 0 ≤ x) :
    weibullSurvival k lam x = Real.exp (-(x / lam) ^ k) :=
  ite_eq_right (not_lt.2 hx)

/-- **Bridge to the canonical Weibull law**: for `0 < k` and `0 < lam`,
`weibullSurvival k lam x` is the survival probability `P(X > x)` of
`ProbabilityTheory.weibullMeasure k lam`, for every `x` (including `x < 0`, where both
sides are `1`, since the Weibull law puts no mass on `(-∞, 0]`). -/
lemma weibullSurvival_eq_weibullMeasure_real_Ioi {k lam x : ℝ} (hk : 0 < k) (hlam : 0 < lam) :
    weibullSurvival k lam x = (weibullMeasure k lam).real (Ioi x) := by
  by_cases hx : 0 ≤ x
  · rw [weibullSurvival_of_nonneg hx, weibullMeasure_real_Ioi hk hlam hx]
  · have hx' : x < 0 := not_le.mp hx
    rw [weibullSurvival_of_neg hx']
    haveI : IsProbabilityMeasure (weibullMeasure k lam) :=
      isProbabilityMeasure_weibullMeasure hk hlam
    have hIic : (weibullMeasure k lam).real (Iic x) = 0 := by
      rw [measureReal_def,
        measure_mono_null (fun y hy => hy.trans hx'.le) (weibullMeasure_Iic_zero k lam),
        ENNReal.toReal_zero]
    have hunion : (weibullMeasure k lam).real univ =
        (weibullMeasure k lam).real (Iic x) + (weibullMeasure k lam).real (Ioi x) := by
      rw [← Iic_union_Ioi (a := x), measureReal_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi]
    rw [probReal_univ, hIic] at hunion
    linarith

/-- **Survival of an actual Weibull variable**: if `T` has law `weibullMeasure k lam`, then
`P(x < T) = weibullSurvival k lam x`, for every `x`. This is how the weakest-link and
size-scaling results below apply to Weibull random variables, rather than only to an assumed
survival function. -/
lemma measureReal_gt_eq_weibullSurvival {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {T : Ω → ℝ} {k lam x : ℝ} (hk : 0 < k) (hlam : 0 < lam)
    (hT : HasLaw T (weibullMeasure k lam) P) :
    P.real {ω | x < T ω} = weibullSurvival k lam x := by
  rw [weibullSurvival_eq_weibullMeasure_real_Ioi hk hlam]
  exact hT.measureReal_eq measurableSet_Ioi

/-- `S(0) = 1` for `k ≠ 0`. -/
lemma weibullSurvival_zero {k : ℝ} (hk : k ≠ 0) (lam : ℝ) : weibullSurvival k lam 0 = 1 := by
  rw [weibullSurvival_of_nonneg le_rfl, zero_div, zero_rpow hk, neg_zero, exp_zero]

/-- The Weibull survival function is antitone, `x ≤ y → S(y) ≤ S(x)`, for `0 ≤ k` and
`0 ≤ lam`. -/
lemma antitone_weibullSurvival {k lam : ℝ} (hk : 0 ≤ k) (hlam : 0 ≤ lam) :
    Antitone (weibullSurvival k lam) := by
  intro x y hxy
  rcases lt_or_ge y 0 with hy | hy
  · rw [weibullSurvival_of_neg hy, weibullSurvival_of_neg (hxy.trans_lt hy)]
  rw [weibullSurvival_of_nonneg hy]
  rcases lt_or_ge x 0 with hx | hx
  · rw [weibullSurvival_of_neg hx, exp_le_one_iff, neg_nonpos]
    exact rpow_nonneg (div_nonneg hy hlam) k
  · rw [weibullSurvival_of_nonneg hx, exp_le_exp, neg_le_neg_iff]
    exact rpow_le_rpow (div_nonneg hx hlam) (div_le_div_of_nonneg_right hxy hlam) hk

/-- `S(x) → 0` as `x → ∞`, for `0 < k` and `0 < lam`. -/
lemma tendsto_weibullSurvival_atTop {k lam : ℝ} (hk : 0 < k) (hlam : 0 < lam) :
    Tendsto (weibullSurvival k lam) atTop (𝓝 0) := by
  have h : Tendsto (fun x => Real.exp (-(x / lam) ^ k)) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_rpow_atTop hk).comp (tendsto_id.atTop_div_const hlam))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [weibullSurvival_of_nonneg hx]

/-- **Assumed power-law hazard**: `-log S(x) = (x / lam) ^ k` for `0 ≤ x`. This holds by the
definition of `weibullSurvival`: the power-law cumulative hazard is the assumed model, and it is
not derived from independence. -/
lemma neg_log_weibullSurvival {k lam x : ℝ} (hx : 0 ≤ x) :
    -Real.log (weibullSurvival k lam x) = (x / lam) ^ k := by
  rw [weibullSurvival_of_nonneg hx, log_exp, neg_neg]

/-- **Weakest-link product theorem (conditional).** A system of `n` links has survival
`system x` at load `x`, and link `i` has survival `link i x`. Independence is the explicit
hypothesis `hindep` on the joint survival: the system survival is the product of the link
survivals. If moreover each link has survival `S`, the system survival is `S x ^ n`, by induction
on `n`. Independence and the power-law hazard are separate hypotheses, neither derived from the
other; `S` is an arbitrary function here. -/
lemma weakestLink_survival_eq_pow {n : ℕ} {link : ℕ → ℝ → ℝ} {S system : ℝ → ℝ}
    (hindep : ∀ x, system x = ∏ i ∈ Finset.range n, link i x)
    (hlink : ∀ i < n, ∀ x, link i x = S x) (x : ℝ) :
    system x = S x ^ n := by
  rw [hindep x]
  clear hindep
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih fun i hi => hlink i (by omega), hlink m (by omega), pow_succ]

/-- Mutually independent link strengths `T i` satisfy the joint-survival hypothesis of
`weakestLink_survival_eq_pow`: the probability that each of the first `n` links survives the
load `x` is the product of the individual survival probabilities. This uses independence only,
and no form of the hazard. -/
lemma measureReal_forall_lt_eq_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {T : ℕ → Ω → ℝ} (hT : iIndepFun T P) (n : ℕ) (x : ℝ) :
    P.real {ω | ∀ i < n, x < T i ω} = ∏ i ∈ Finset.range n, P.real {ω | x < T i ω} := by
  have hset : {ω | ∀ i < n, x < T i ω} = ⋂ i ∈ Finset.range n, T i ⁻¹' Ioi x := by
    ext ω
    simp
  rw [hset, measureReal_def, hT.measure_inter_preimage_eq_mul (Finset.range n)
    (sets := fun _ => Ioi x) fun _ _ => measurableSet_Ioi, ENNReal.toReal_prod]
  rfl

/-- **Size scaling (conditional).** A specimen of volume `V` behaves as `m = V / V₀` independent
copies of a reference volume `V₀`: the hypothesis `hindep` says that its survival is the product
of the survivals of `m` pieces, with `V / V₀` a natural number, and each piece has the reference
survival `Sref`. Then the specimen survival is `Sref x ^ (V / V₀)`. Independence and the
power-law hazard are separate hypotheses, neither derived from the other. -/
lemma sizeScaling_survival_eq_rpow {V V₀ : ℝ} {m : ℕ} (hm : V / V₀ = m)
    {piece : ℕ → ℝ → ℝ} {Sref specimen : ℝ → ℝ}
    (hindep : ∀ x, specimen x = ∏ i ∈ Finset.range m, piece i x)
    (hpiece : ∀ i < m, ∀ x, piece i x = Sref x) (x : ℝ) :
    specimen x = Sref x ^ (V / V₀) := by
  rw [hm, rpow_natCast]
  exact weakestLink_survival_eq_pow hindep hpiece x

/-- **Weibull form under both hypotheses**: for `0 < c`, the `c`-th power of a Weibull survival
function is the Weibull survival function with the same shape and scale `lam / c ^ (1 / k)`.
With `c = n` in `weakestLink_survival_eq_pow`, or `c = V / V₀` in
`sizeScaling_survival_eq_rpow`, independent components with the power-law hazard give a system of
Weibull form. Independence supplies the power, and the power-law hazard of the components
supplies the Weibull form. -/
lemma weibullSurvival_rpow {k lam c : ℝ} (hk : 0 < k) (hlam : 0 < lam) (hc : 0 < c) (x : ℝ) :
    weibullSurvival k lam x ^ c = weibullSurvival k (lam / c ^ (1 / k)) x := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [weibullSurvival_of_neg hx, weibullSurvival_of_neg hx, one_rpow]
  · rw [weibullSurvival_of_nonneg hx, weibullSurvival_of_nonneg hx, ← exp_mul]
    have hck : (c ^ (1 / k)) ^ k = c := by
      rw [← rpow_mul hc.le, one_div_mul_cancel hk.ne', rpow_one]
    have h : (x / (lam / c ^ (1 / k))) ^ k = (x / lam) ^ k * c := by
      rw [div_div_eq_mul_div, div_rpow (x := x * c ^ (1 / k)) (by positivity) hlam.le,
        mul_rpow hx (by positivity), hck, div_rpow hx hlam.le]
      ring
    rw [h, neg_mul]

/-! ## E. JMAK void probability -/

/-- The stipulated JMAK void probability `exp (-kappa * volume)`: the probability that a region
of the given volume contains no nucleus, for the nucleation intensity `kappa`. It is a
STIPULATED model, not derived from a point process. Constructing a continuum Poisson point
process and deriving this void law from it is a separately scoped optional extension; it is not
part of this file and is not claimed. -/
noncomputable def voidProbability (kappa volume : ℝ) : ℝ :=
  Real.exp (-kappa * volume)

/-- A region of zero volume is void with probability `1`. -/
lemma voidProbability_zero (kappa : ℝ) : voidProbability kappa 0 = 1 := by
  simp [voidProbability]

/-- The void probability is antitone in the volume, for `0 ≤ kappa`. -/
lemma antitone_voidProbability {kappa : ℝ} (hkappa : 0 ≤ kappa) :
    Antitone (voidProbability kappa) := by
  intro v w hvw
  simp only [voidProbability, exp_le_exp]
  nlinarith

/-- The void probability tends to `0` as the volume tends to `∞`, for `0 < kappa`. -/
lemma tendsto_voidProbability_atTop {kappa : ℝ} (hkappa : 0 < kappa) :
    Tendsto (voidProbability kappa) atTop (𝓝 0) := by
  refine (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hkappa)).congr
    fun v => ?_
  simp [voidProbability, neg_mul]

/-- The transformed fraction `1 - voidProbability kappa volume` lies in `[0, 1]`, for
`0 ≤ kappa` and `0 ≤ volume`. -/
lemma one_sub_voidProbability_mem_Icc {kappa volume : ℝ} (hkappa : 0 ≤ kappa)
    (hvolume : 0 ≤ volume) : 1 - voidProbability kappa volume ∈ Icc 0 1 := by
  have h1 : voidProbability kappa volume ≤ 1 := by
    rw [voidProbability, exp_le_one_iff]
    nlinarith
  have h0 : 0 < voidProbability kappa volume := exp_pos _
  constructor <;> linarith

/-- **Avrami substitution**: if the extended volume `kappa * volume` is `K * t ^ n`, the
transformed fraction `1 - voidProbability kappa volume` is `1 - exp (-K * t ^ n)`. This is a
substitution into the stipulated void law and needs no hypothesis on `t`, `K` or `n`; no
point-process derivation is claimed. -/
lemma one_sub_voidProbability_eq_avrami {kappa volume K t n : ℝ}
    (hext : kappa * volume = K * t ^ n) :
    1 - voidProbability kappa volume = 1 - Real.exp (-K * t ^ n) := by
  rw [voidProbability, neg_mul, hext, ← neg_mul]

/-! ## F. Maxwell speed density -/

/-- The Maxwell speed density with scale `a` (for a gas, `a ^ 2 = k_B T / m`):
`√(2 / π) v ^ 2 / a ^ 3 exp (-v ^ 2 / (2 a ^ 2))`. Convention: the formula is used for `0 < a`
and `v > 0`, with no piecewise extension. Every integral below is over `Set.Ioi 0`, and the
formula is not a probability density on all of `ℝ`. -/
noncomputable def maxwellSpeedPDF (a : ℝ) (v : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * v ^ 2 / a ^ 3 * Real.exp (-v ^ 2 / (2 * a ^ 2))

/-- The Maxwell speed density is nonnegative, for `0 ≤ a`. -/
lemma maxwellSpeedPDF_nonneg {a : ℝ} (ha : 0 ≤ a) (v : ℝ) : 0 ≤ maxwellSpeedPDF a v := by
  unfold maxwellSpeedPDF
  positivity

/-- The Gaussian moment `∫ v in (0, ∞), v ^ q exp (-v ^ 2 / (2 a ^ 2))`, from Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow`. -/
private lemma integral_rpow_mul_exp_neg_sq_div {a q : ℝ} (ha : a ≠ 0) (hq : -1 < q) :
    ∫ v in Ioi 0, v ^ q * Real.exp (-v ^ 2 / (2 * a ^ 2)) =
      (2 * a ^ 2) ^ ((q + 1) / 2) * (1 / 2) * Gamma ((q + 1) / 2) := by
  have hc : 0 < 2 * a ^ 2 := by positivity
  have hfun : ∀ v : ℝ, -v ^ 2 / (2 * a ^ 2) = -(2 * a ^ 2)⁻¹ * v ^ (2 : ℝ) := by
    intro v
    rw [rpow_two]
    ring
  simp_rw [hfun]
  rw [integral_rpow_mul_exp_neg_mul_rpow two_pos hq (inv_pos.2 hc), neg_div,
    rpow_neg (inv_pos.2 hc).le, inv_rpow hc.le, inv_inv]

/-- `(2 a ^ 2) ^ (k + 1 / 2) = (2 a ^ 2) ^ k √2 a`, for `0 < a`. -/
private lemma two_mul_sq_rpow_nat_add_half {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (2 * a ^ 2) ^ ((k : ℝ) + 1 / 2) = (2 * a ^ 2) ^ k * (√2 * a) := by
  rw [rpow_add (by positivity), rpow_natCast, ← sqrt_eq_rpow, sqrt_mul (by norm_num),
    sqrt_sq ha.le]

/-- **Normalization of the Maxwell speed density**: `∫ v in (0, ∞), maxwellSpeedPDF a v = 1` for
`0 < a`, from Mathlib's Gamma-function integral and `Γ(3/2) = √π / 2`. -/
lemma integral_maxwellSpeedPDF {a : ℝ} (ha : 0 < a) :
    ∫ v in Ioi 0, maxwellSpeedPDF a v = 1 := by
  have hfun : ∀ v : ℝ, maxwellSpeedPDF a v =
      √(2 / π) / a ^ 3 * (v ^ (2 : ℝ) * Real.exp (-v ^ 2 / (2 * a ^ 2))) := by
    intro v
    rw [maxwellSpeedPDF, rpow_two]
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_rpow_mul_exp_neg_sq_div ha.ne' (by norm_num),
    show ((2 : ℝ) + 1) / 2 = ((1 : ℕ) : ℝ) + 1 / 2 by norm_num, Gamma_nat_add_half,
    two_mul_sq_rpow_nat_add_half ha, sqrt_div' 2 pi_pos.le]
  have hpi : √π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  field_simp
  norm_num [Nat.doubleFactorial]

/-- **Second moment of the Maxwell speed density**: `∫ v in (0, ∞), v ^ 2 maxwellSpeedPDF a v =
3 a ^ 2` for `0 < a`, that is `(1/2) m ⟨v ^ 2⟩ = (3/2) k_B T`. From the same Gamma-function
integral and `Γ(5/2) = 3 √π / 4`. -/
lemma integral_sq_mul_maxwellSpeedPDF {a : ℝ} (ha : 0 < a) :
    ∫ v in Ioi 0, v ^ 2 * maxwellSpeedPDF a v = 3 * a ^ 2 := by
  have hfun : ∀ v : ℝ, v ^ 2 * maxwellSpeedPDF a v =
      √(2 / π) / a ^ 3 * (v ^ (4 : ℝ) * Real.exp (-v ^ 2 / (2 * a ^ 2))) := by
    intro v
    rw [maxwellSpeedPDF, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_rpow_mul_exp_neg_sq_div ha.ne' (by norm_num),
    show ((4 : ℝ) + 1) / 2 = ((2 : ℕ) : ℝ) + 1 / 2 by norm_num, Gamma_nat_add_half,
    two_mul_sq_rpow_nat_add_half ha, sqrt_div' 2 pi_pos.le]
  have hpi : √π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  field_simp
  norm_num [Nat.doubleFactorial]

end MathlibExt.Probability.ContinuousDistributions
