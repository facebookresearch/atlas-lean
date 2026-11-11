/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Poisson.Basic
public import MathlibExt.Probability.Statistics.ExactTests.TailPValue
public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Cast

/-!
# Poisson count data: likelihood, deviance, and the exact conditional rate test

## The count model

This file restates, in its own terms, the minimal count model of RNA-seq-style differential
expression. A gene with expression rate `λ ≥ 0` (expected reads per unit of library size) is
observed in a library of size `s > 0`; its read count is Poisson with mean `s λ`. On the log
scale the mean is `s · exp η` with linear predictor `η = log λ` and offset `log s`
(`countMean s η`). Counts of several libraries of one condition are independent.

## Likelihood, score and deviance

* `log_poissonMeasure_real_singleton`: `log P(Y = y) = y log r - r - log y!` for `Y ~ Po(r)`,
  `r > 0`.
* `log_poissonMeasure_countMean`, `hasDerivAt_log_poissonMeasure_countMean`: with the offset,
  the log-likelihood is `y (log s + η) - s e^η - log y!` and the score is `y - s e^η`.
* `hasDerivAt_sum_log_poissonMeasure_countMean`, `sum_score_eq_zero_iff`: for replicate libraries
  `sᵢ` sharing one rate, the score is `∑ yᵢ - e^η ∑ sᵢ`, which vanishes exactly at
  `e^η = ∑ yᵢ / ∑ sᵢ`.
* `poissonDeviance y μ = 2 (y log (y / μ) - (y - μ))`, the unit Poisson deviance (at `y = 0` it
  is `2 μ`, by Lean's `log 0 = 0`). `poissonDeviance_eq_two_mul_log_ratio`: it is twice the
  log-likelihood ratio of the saturated fit `μ = y` against `μ`. `poissonDeviance_nonneg` and
  `poissonDeviance_eq_zero_iff`: it is nonnegative and vanishes only at `y = μ`.

## The exact conditional test

To compare one gene between two conditions with (pooled) library sizes `s₁, s₂`, observe
independent counts `X ~ Po(s₁ r₁)` and `Y ~ Po(s₂ r₂)` and test `r₁ = r₂ = r`. The total `X + Y`
is sufficient for the nuisance rate `r`, and conditioning on it removes `r`: given `X + Y = n`,
`X ~ Bin(n, s₁ / (s₁ + s₂))`. Rejecting for large `X` gives the exact conditional (binomial)
test of Przyborowski and Wileński.

* `measureReal_add_eq_inter_eq`: `P(X + Y = n, X = k) = Bin(n, s₁/(s₁+s₂)){k} P(X + Y = n)` for
  every rate `r ≥ 0`.
* `cond_measureReal_eq_binomial`, `hasLaw_cond_binomial`: given a total of positive probability,
  `X` is `Bin(n, s₁ / (s₁ + s₂))`; `measure_add_eq_ne_zero`: every total has positive
  probability when `r > 0`.
* `countExactPValue`: the one-sided exact p-value `Bin(X + Y, s₁/(s₁+s₂)) {j ≥ X}`.
* `isValidPValue_countExact_cond`: valid conditionally on every total.
* `isValidPValue_countExactPValue`: valid unconditionally, for every nuisance rate `r ≥ 0`.
* `integral_fdp_bhRejections_countExact_le_of_arbitrary_dependence`: over `m` genes, BH at level
  `q / H_m` on the exact p-values has FDR `≤ q |H0| / m` under arbitrary dependence
  (Benjamini–Yekutieli); `integral_fdp_bhRejections_countExact_le`: BH at level `q` suffices when
  the genes' count pairs are independent (Benjamini–Hochberg).

## Scope

Calibration is proved for the Poisson null only. Under negative-binomial overdispersion
(biological variation between replicates), the conditional law of `X` given `X + Y` is not
binomial, and nothing here asserts that the exact Poisson test is valid there. The test is
one-sided (higher rate in condition 1); the other side follows by swapping the conditions.

## References

* M. Przyborowski and H. Wileński, *Homogeneity of results in testing samples from Poisson
  series*, Biometrika 31 (1940), 313–323.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §4.5 and Lemma 3.3.1.
* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd ed., Chapman & Hall (1989),
  Ch. 6 (log-linear models for counts).
* M. D. Robinson and G. K. Smyth, *Small-sample estimation of negative binomial dispersion, with
  applications to SAGE data*, Biostatistics 9 (2008), 321–332 (exact tests for count data).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset MathlibExt.Probability.Statistics.ExactTests
open scoped NNReal unitInterval Nat

namespace MathlibExt.Probability.Statistics.GLM.CountData

/-! ### Likelihood and score -/

/-- The Poisson mean `s · exp η` of a count with library size (offset scale) `s` and linear
predictor `η = log λ`, as a rate in `ℝ≥0`. -/
noncomputable def countMean (s : ℝ≥0) (η : ℝ) : ℝ≥0 :=
  ⟨s * exp η, mul_nonneg s.2 (exp_pos η).le⟩

@[simp]
theorem coe_countMean (s : ℝ≥0) (η : ℝ) : (countMean s η : ℝ) = s * exp η := rfl

/-- **Poisson log-likelihood.** For `Y ~ Po(r)` with `r > 0`,
`log P(Y = y) = y log r - r - log y!`. -/
theorem log_poissonMeasure_real_singleton {r : ℝ≥0} (hr : 0 < r) (y : ℕ) :
    log (Po(r).real {y}) = y * log r - r - log (y ! : ℝ) := by
  have hr' : (0 : ℝ) < r := hr
  have hfac : (0 : ℝ) < (y ! : ℝ) := by exact_mod_cast Nat.factorial_pos y
  rw [poissonMeasure_real_singleton, log_div (mul_pos (exp_pos _) (pow_pos hr' _)).ne' hfac.ne',
    log_mul (exp_pos _).ne' (pow_pos hr' _).ne', log_exp, log_pow]
  ring

/-- **Log-likelihood with a library-size offset.** For a count `Y ~ Po(s e^η)` with `s > 0`,
`log P(Y = y) = y (log s + η) - s e^η - log y!`. -/
theorem log_poissonMeasure_countMean {s : ℝ≥0} (hs : 0 < s) (η : ℝ) (y : ℕ) :
    log (Po(countMean s η).real {y}) = y * (log s + η) - s * exp η - log (y ! : ℝ) := by
  have hs' : (0 : ℝ) < s := hs
  have hpos : 0 < countMean s η := by
    change (0 : ℝ) < s * exp η
    positivity
  rw [log_poissonMeasure_real_singleton hpos, coe_countMean,
    log_mul hs'.ne' (exp_pos η).ne', log_exp]

/-- **Score of the offset Poisson model.** The derivative in the linear predictor `η` of the
log-likelihood of a count `y` with library size `s > 0` is `y - s e^η`. -/
theorem hasDerivAt_log_poissonMeasure_countMean {s : ℝ≥0} (hs : 0 < s) (y : ℕ) (η : ℝ) :
    HasDerivAt (fun η => log (Po(countMean s η).real {y})) (y - s * exp η) η := by
  have h : (fun η => log (Po(countMean s η).real {y})) =
      fun η => y * (log s + η) - s * exp η - log (y ! : ℝ) :=
    funext fun η => log_poissonMeasure_countMean hs η y
  rw [h]
  have := ((((hasDerivAt_id η).const_add (log (s : ℝ))).const_mul (y : ℝ)).sub
    ((hasDerivAt_exp η).const_mul (s : ℝ))).sub_const (log (y ! : ℝ))
  simpa using this

/-- **Score of replicate libraries sharing one rate.** For independent counts `yᵢ` from
libraries of sizes `sᵢ > 0` with a common linear predictor `η`, the derivative of the joint
log-likelihood `∑ᵢ log P(Yᵢ = yᵢ)` is `∑ᵢ yᵢ - e^η ∑ᵢ sᵢ`. -/
theorem hasDerivAt_sum_log_poissonMeasure_countMean {ι : Type*} (t : Finset ι) {s : ι → ℝ≥0}
    (hs : ∀ i ∈ t, 0 < s i) (y : ι → ℕ) (η : ℝ) :
    HasDerivAt (fun η => ∑ i ∈ t, log (Po(countMean (s i) η).real {y i}))
      ((∑ i ∈ t, (y i : ℝ)) - exp η * ∑ i ∈ t, (s i : ℝ)) η := by
  have h := HasDerivAt.fun_sum (u := t) fun i hi =>
    hasDerivAt_log_poissonMeasure_countMean (hs i hi) (y i) η
  convert h using 1
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The score equation.** With total library size `∑ sᵢ > 0`, the replicate score
`∑ yᵢ - e^η ∑ sᵢ` vanishes exactly when the fitted rate `e^η` is the pooled rate
`∑ yᵢ / ∑ sᵢ`. -/
theorem sum_score_eq_zero_iff {ι : Type*} (t : Finset ι) {s : ι → ℝ≥0}
    (hs : 0 < ∑ i ∈ t, (s i : ℝ)) (y : ι → ℕ) (η : ℝ) :
    (∑ i ∈ t, (y i : ℝ)) - exp η * ∑ i ∈ t, (s i : ℝ) = 0 ↔
      exp η = (∑ i ∈ t, (y i : ℝ)) / ∑ i ∈ t, (s i : ℝ) := by
  rw [eq_div_iff hs.ne', sub_eq_zero, eq_comm]

/-! ### Deviance -/

/-- The unit Poisson deviance `2 (y log (y / μ) - (y - μ))` of an observation `y` against a
fitted mean `μ`. At `y = 0` it is `2 μ`, by Lean's convention `log 0 = 0`. Meaningful for
`y ≥ 0`, `μ > 0`. -/
noncomputable def poissonDeviance (y μ : ℝ) : ℝ :=
  2 * (y * log (y / μ) - (y - μ))

/-- The deviance of a zero count is twice the fitted mean. -/
theorem poissonDeviance_zero_left (μ : ℝ) : poissonDeviance 0 μ = 2 * μ := by
  simp [poissonDeviance]

/-- **Deviance as a likelihood ratio.** For a count `y` and a fitted rate `r > 0`, the unit
deviance is twice the log-likelihood ratio of the saturated fit (rate `y`) against rate `r`. -/
theorem poissonDeviance_eq_two_mul_log_ratio {r : ℝ≥0} (hr : 0 < r) (y : ℕ) :
    poissonDeviance y r =
      2 * (log (Po((y : ℝ≥0)).real {y}) - log (Po(r).real {y})) := by
  rw [log_poissonMeasure_real_singleton hr]
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [poissonDeviance, poissonMeasure_real_singleton]
  · have hy' : (0 : ℝ≥0) < (y : ℝ≥0) := by exact_mod_cast hy
    have hyr : (0 : ℝ) < y := by exact_mod_cast hy
    have hr' : (0 : ℝ) < r := hr
    rw [log_poissonMeasure_real_singleton hy', poissonDeviance, log_div hyr.ne' hr'.ne']
    push_cast
    ring

/-- The deviance as `2 y (x - 1 - log x)` with `x = μ / y`, for `y > 0`. -/
private lemma poissonDeviance_eq_mul {y μ : ℝ} (hy : 0 < y) (hμ : 0 < μ) :
    poissonDeviance y μ = 2 * y * (μ / y - 1 - log (μ / y)) := by
  rw [poissonDeviance, log_div hy.ne' hμ.ne', log_div hμ.ne' hy.ne']
  field_simp
  ring

/-- **The deviance is nonnegative** for `y ≥ 0` and `μ > 0`. -/
theorem poissonDeviance_nonneg {y μ : ℝ} (hy : 0 ≤ y) (hμ : 0 < μ) : 0 ≤ poissonDeviance y μ := by
  rcases hy.eq_or_lt with rfl | hy
  · rw [poissonDeviance_zero_left]
    positivity
  · rw [poissonDeviance_eq_mul hy hμ]
    have := log_le_sub_one_of_pos (div_pos hμ hy)
    have : 0 ≤ μ / y - 1 - log (μ / y) := by linarith
    positivity

/-- **The deviance vanishes only at a perfect fit:** for `y ≥ 0` and `μ > 0`,
`poissonDeviance y μ = 0 ↔ y = μ`. -/
theorem poissonDeviance_eq_zero_iff {y μ : ℝ} (hy : 0 ≤ y) (hμ : 0 < μ) :
    poissonDeviance y μ = 0 ↔ y = μ := by
  constructor
  · intro h
    rcases hy.eq_or_lt with rfl | hy
    · rw [poissonDeviance_zero_left] at h
      linarith
    · by_contra hne
      have hx : μ / y ≠ 1 := fun hx => hne ((div_eq_one_iff_eq hy.ne').1 hx).symm
      have := log_lt_sub_one_of_pos (div_pos hμ hy) hx
      rw [poissonDeviance_eq_mul hy hμ] at h
      have : 0 < 2 * y * (μ / y - 1 - log (μ / y)) := by
        have : 0 < μ / y - 1 - log (μ / y) := by linarith
        positivity
      linarith
  · rintro rfl
    simp [poissonDeviance, div_self hμ.ne']

/-! ### The exact conditional test for equal rates -/

section ExactTest

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℕ} {s₁ s₂ r : ℝ≥0}

/-- The library fraction `s₁ / (s₁ + s₂)` of condition 1, as a probability. Under equal rates it
is the success probability of the conditional binomial law. (If `s₁ + s₂ = 0` it is `0`, by
Lean's division by zero.) -/
noncomputable def libraryFraction (s₁ s₂ : ℝ≥0) : I :=
  ⟨(s₁ : ℝ) / (s₁ + s₂), div_nonneg s₁.2 (add_nonneg s₁.2 s₂.2),
    div_le_one_of_le₀ (le_add_of_nonneg_right s₂.2) (add_nonneg s₁.2 s₂.2)⟩

@[simp]
theorem coe_libraryFraction (s₁ s₂ : ℝ≥0) :
    (libraryFraction s₁ s₂ : ℝ) = (s₁ : ℝ) / (s₁ + s₂) := rfl

/-- The Poisson–binomial factorization behind the test: for `k ≤ n` and `s₁ + s₂ > 0`,
`Po(s₁ r){k} Po(s₂ r){n - k} = Bin(n, s₁ / (s₁ + s₂)){k} Po((s₁ + s₂) r){n}`, for every rate
`r ≥ 0`. -/
private lemma poisson_mul_poisson_eq (hs : 0 < s₁ + s₂) {k n : ℕ} (hk : k ≤ n) :
    Po(s₁ * r).real {k} * Po(s₂ * r).real {n - k} =
      Bin(n, libraryFraction s₁ s₂).real {k} * Po((s₁ + s₂) * r).real {n} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hS : (0 : ℝ) < s₁ + s₂ := by exact_mod_cast hs
  rw [Nat.add_sub_cancel_left, poissonMeasure_real_singleton, poissonMeasure_real_singleton,
    binomial_real_singleton, poissonMeasure_real_singleton, coe_libraryFraction,
    Nat.add_sub_cancel_left, Nat.cast_add_choose]
  have h1 : 1 - (s₁ : ℝ) / (s₁ + s₂) = s₂ / (s₁ + s₂) := by field_simp; ring
  rw [h1]
  push_cast
  have he : exp (-((s₁ : ℝ) * r)) * exp (-((s₂ : ℝ) * r)) = exp (-((s₁ + s₂) * r)) := by
    rw [← exp_add]; ring_nf
  have hk' : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hj' : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hn' : (0 : ℝ) < ((k + j) ! : ℝ) := by exact_mod_cast Nat.factorial_pos (k + j)
  rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, pow_add, pow_add, ← he]
  field_simp

/-- Independence gives the joint mass of two Poisson counts. -/
private lemma measureReal_eq_and_eq {r₁ r₂ : ℝ≥0} (hX : HasLaw X Po(r₁) μ) (hY : HasLaw Y Po(r₂) μ)
    (hXY : IndepFun X Y μ) (k j : ℕ) :
    μ.real {ω | X ω = k ∧ Y ω = j} = Po(r₁).real {k} * Po(r₂).real {j} := by
  have hX' : μ.real {ω | X ω = k} = Po(r₁).real {k} :=
    hX.measureReal_eq (p := (· = k)) (measurableSet_singleton k)
  have hY' : μ.real {ω | Y ω = j} = Po(r₂).real {j} :=
    hY.measureReal_eq (p := (· = j)) (measurableSet_singleton j)
  have := hXY.measure_inter_preimage_eq_mul {k} {j} (measurableSet_singleton k)
    (measurableSet_singleton j)
  rw [← hX', ← hY']
  simp only [measureReal_def]
  rw [← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal this

omit [MeasurableSpace Ω] in
private lemma setOf_add_eq_inter_eq {n k : ℕ} (hk : k ≤ n) :
    {ω | X ω + Y ω = n} ∩ {ω | X ω = k} = {ω | X ω = k ∧ Y ω = n - k} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  omega

omit [MeasurableSpace Ω] in
private lemma setOf_add_eq_inter_eq_of_lt {n k : ℕ} (hk : n < k) :
    {ω | X ω + Y ω = n} ∩ {ω | X ω = k} = ∅ := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  omega

/-- **Binomial conditioning, joint form.** Let `X ~ Po(s₁ r)` and `Y ~ Po(s₂ r)` be independent
counts of one gene in two conditions with library sizes `s₁, s₂` (`s₁ + s₂ > 0`) and a common
rate `r ≥ 0`. Then for every total `n` and cell `k`,
`P(X + Y = n, X = k) = Bin(n, s₁ / (s₁ + s₂)){k} · P(X + Y = n)`. This needs no positivity of
`r` and no conditioning on a null event. -/
theorem measureReal_add_eq_inter_eq (hs : 0 < s₁ + s₂) (hX : HasLaw X Po(s₁ * r) μ)
    (hY : HasLaw Y Po(s₂ * r) μ) (hXY : IndepFun X Y μ) (n k : ℕ) :
    μ.real ({ω | X ω + Y ω = n} ∩ {ω | X ω = k}) =
      Bin(n, libraryFraction s₁ s₂).real {k} * μ.real {ω | X ω + Y ω = n} := by
  have hsum : μ.real {ω | X ω + Y ω = n} = Po((s₁ + s₂) * r).real {n} := by
    have h := hXY.hasLaw_add_poissonMeasure hX hY
    rw [← add_mul] at h
    exact h.measureReal_eq (p := (· = n)) (measurableSet_singleton n)
  rw [hsum]
  rcases le_or_gt k n with hk | hk
  · rw [setOf_add_eq_inter_eq hk, measureReal_eq_and_eq hX hY hXY, poisson_mul_poisson_eq hs hk]
  · rw [setOf_add_eq_inter_eq_of_lt hk, measureReal_empty, binomial_real_singleton,
      Nat.choose_eq_zero_of_lt hk]
    simp

/-- **Binomial conditioning.** Under the hypotheses of `measureReal_add_eq_inter_eq`, given a
total `X + Y = n` of positive probability, the condition-1 count is binomial:
`P(X = k | X + Y = n) = Bin(n, s₁ / (s₁ + s₂)){k}`. The law does not depend on the nuisance rate
`r`.

Source: Lehmann–Romano (2005), §4.5; Przyborowski–Wileński (1940). -/
theorem cond_measureReal_eq_binomial (hs : 0 < s₁ + s₂) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasLaw X Po(s₁ * r) μ) (hY : HasLaw Y Po(s₂ * r) μ) (hXY : IndepFun X Y μ) {n : ℕ}
    (hn : μ {ω | X ω + Y ω = n} ≠ 0) (k : ℕ) :
    (μ[|{ω | X ω + Y ω = n}]).real {ω | X ω = k} = Bin(n, libraryFraction s₁ s₂).real {k} := by
  have := hX.isFiniteMeasure
  have hS : MeasurableSet {ω | X ω + Y ω = n} := (hXm.add hYm) (measurableSet_singleton n)
  have hpos : μ.real {ω | X ω + Y ω = n} ≠ 0 :=
    (ENNReal.toReal_ne_zero).2 ⟨hn, measure_ne_top μ _⟩
  have hcond : (μ[|{ω | X ω + Y ω = n}]).real {ω | X ω = k} =
      (μ.real {ω | X ω + Y ω = n})⁻¹ * μ.real ({ω | X ω + Y ω = n} ∩ {ω | X ω = k}) := by
    simp only [measureReal_def, cond_apply hS, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [hcond, measureReal_add_eq_inter_eq hs hX hY hXY]
  field_simp

/-- A positive rate makes every total `X + Y = n` have positive probability. -/
theorem measure_add_eq_ne_zero (hs : 0 < s₁ + s₂) (hr : 0 < r) (hX : HasLaw X Po(s₁ * r) μ)
    (hY : HasLaw Y Po(s₂ * r) μ) (hXY : IndepFun X Y μ) (n : ℕ) :
    μ {ω | X ω + Y ω = n} ≠ 0 := by
  have h := hXY.hasLaw_add_poissonMeasure hX hY
  rw [← add_mul] at h
  have h2 : μ.real {ω | X ω + Y ω = n} = Po((s₁ + s₂) * r).real {n} :=
    h.measureReal_eq (p := (· = n)) (measurableSet_singleton n)
  have hpos := poissonMeasure_real_singleton_pos (r := (s₁ + s₂) * r) n (mul_pos hs hr)
  rw [← h2] at hpos
  exact fun h0 => hpos.ne' (by simp [measureReal_def, h0])

/-- **Binomial conditioning, as a law.** Given a total `X + Y = n` of positive probability, the
condition-1 count has law `Bin(n, s₁ / (s₁ + s₂))` under the conditional measure. -/
theorem hasLaw_cond_binomial (hs : 0 < s₁ + s₂) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasLaw X Po(s₁ * r) μ) (hY : HasLaw Y Po(s₂ * r) μ) (hXY : IndepFun X Y μ) {n : ℕ}
    (hn : μ {ω | X ω + Y ω = n} ≠ 0) :
    HasLaw X Bin(n, libraryFraction s₁ s₂) (μ[|{ω | X ω + Y ω = n}]) where
  aemeasurable := hXm.aemeasurable
  map_eq := by
    have := hX.isFiniteMeasure
    have := cond_isProbabilityMeasure hn
    refine Measure.ext_of_measureReal_singleton fun k => ?_
    rw [map_measureReal_apply hXm (measurableSet_singleton k)]
    exact cond_measureReal_eq_binomial hs hXm hYm hX hY hXY hn k

/-- The exact conditional upper tail at a pair of counts `c = (x, y)`: the
`Bin(x + y, s₁ / (s₁ + s₂))` probability of a condition-1 count at least `x`. -/
noncomputable def countExactTail (s₁ s₂ : ℝ≥0) (c : ℕ × ℕ) : ℝ :=
  upperTail Bin(c.1 + c.2, libraryFraction s₁ s₂) c.1

/-- The one-sided exact conditional p-value for a higher rate in condition 1: given the observed
total `X ω + Y ω`, the `Bin(X ω + Y ω, s₁ / (s₁ + s₂))` probability of a condition-1 count at least
as large as the observed `X ω`. -/
noncomputable def countExactPValue (s₁ s₂ : ℝ≥0) (X Y : Ω → ℕ) (ω : Ω) : ℝ :=
  countExactTail s₁ s₂ (X ω, Y ω)

omit [MeasurableSpace Ω] in
/-- On the event `X + Y = n` the exact p-value is the fixed-total upper-tail p-value. -/
theorem countExactPValue_eq_upperTailPValue {n : ℕ} {ω : Ω} (hω : X ω + Y ω = n) :
    countExactPValue s₁ s₂ X Y ω = upperTailPValue Bin(n, libraryFraction s₁ s₂) X ω := by
  rw [countExactPValue, countExactTail, upperTailPValue, ← hω]

/-- The exact p-value is measurable. -/
theorem measurable_countExactPValue (hXm : Measurable X) (hYm : Measurable Y) :
    Measurable (countExactPValue s₁ s₂ X Y) :=
  (measurable_of_countable (countExactTail s₁ s₂)).comp (hXm.prodMk hYm)

/-- **Conditional validity of the exact test.** Under equal rates `r > 0` in the two conditions,
the fixed-total upper-tail p-value is valid conditionally on every total `X + Y = n`, whatever
the nuisance rate `r`. -/
theorem isValidPValue_countExact_cond (hs : 0 < s₁ + s₂) (hr : 0 < r) (hXm : Measurable X)
    (hYm : Measurable Y) (hX : HasLaw X Po(s₁ * r) μ) (hY : HasLaw Y Po(s₂ * r) μ)
    (hXY : IndepFun X Y μ) (n : ℕ) :
    MultipleTesting.IsValidPValue (μ[|{ω | X ω + Y ω = n}])
      (upperTailPValue Bin(n, libraryFraction s₁ s₂) X) :=
  isValidPValue_upperTailPValue
    (hasLaw_cond_binomial hs hXm hYm hX hY hXY (measure_add_eq_ne_zero hs hr hX hY hXY n))

/-- **Validity of the exact conditional Poisson test.** Let `X ~ Po(s₁ r)` and `Y ~ Po(s₂ r)` be
independent counts of one gene in two conditions with library sizes `s₁, s₂` (`s₁ + s₂ > 0`) and
a common rate `r ≥ 0` (the null hypothesis of equal expression). Then the exact p-value
`countExactPValue s₁ s₂ X Y` is valid: `P(p ≤ t) ≤ t` for every `t ∈ [0, 1]`, whatever `r`
(including `r = 0`, a gene that is never expressed).

The proof averages the conditional guarantee over the total `X + Y`. This is a statement about
the Poisson null only: under negative-binomial overdispersion the conditional law of `X` given
`X + Y` is no longer binomial and no calibration is asserted.

Source: Przyborowski–Wileński (1940); Lehmann–Romano (2005), §4.5 and Lemma 3.3.1. -/
theorem isValidPValue_countExactPValue [IsProbabilityMeasure μ] (hs : 0 < s₁ + s₂)
    (hXm : Measurable X) (hYm : Measurable Y) (hX : HasLaw X Po(s₁ * r) μ)
    (hY : HasLaw Y Po(s₂ * r) μ) (hXY : IndepFun X Y μ) :
    MultipleTesting.IsValidPValue μ (countExactPValue s₁ s₂ X Y) := by
  intro t ht
  set S : ℕ → Set Ω := fun n => {ω | X ω + Y ω = n} with hSdef
  set A : ℕ → Set Ω := fun n => X ⁻¹' {k | upperTail Bin(n, libraryFraction s₁ s₂) k ≤ t}
    with hAdef
  have hSm (n : ℕ) : MeasurableSet (S n) := (hXm.add hYm) (measurableSet_singleton n)
  have hAm (n : ℕ) : MeasurableSet (A n) := hXm (MeasurableSet.of_discrete)
  have hSdisj : Pairwise (Function.onFun Disjoint S) := fun i j hij =>
    Set.disjoint_left.2 fun ω hi hj => hij (hi.symm.trans hj)
  have hset : {ω | countExactPValue s₁ s₂ X Y ω ≤ t} = ⋃ n, S n ∩ A n := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, hSdef,
      hAdef, countExactPValue, countExactTail]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
  have hbound (n : ℕ) : μ (S n ∩ A n) ≤ ENNReal.ofReal t * μ (S n) := by
    by_cases hn : μ (S n) = 0
    · rw [hn, mul_zero]
      exact (measure_mono Set.inter_subset_left).trans hn.le
    · rw [← cond_mul_eq_inter (hSm n) (A n) μ]
      exact mul_le_mul_left
        (isValidPValue_upperTailPValue (hasLaw_cond_binomial hs hXm hYm hX hY hXY hn) t ht) _
  rw [hset, measure_iUnion (fun i j hij => (hSdisj hij).mono Set.inter_subset_left
    Set.inter_subset_left) fun n => (hSm n).inter (hAm n)]
  calc ∑' n, μ (S n ∩ A n) ≤ ∑' n, ENNReal.ofReal t * μ (S n) := ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal t * μ (⋃ n, S n) := by rw [ENNReal.tsum_mul_left, measure_iUnion hSdisj hSm]
    _ ≤ ENNReal.ofReal t * 1 := mul_le_mul_right prob_le_one _
    _ = ENNReal.ofReal t := mul_one _

end ExactTest

/-! ### Many genes: false discovery rate control -/

section MultipleTesting

open MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m : ℕ} {s₁ s₂ : ℝ≥0}

/-- **Exact tests of many genes under arbitrary dependence (Benjamini–Yekutieli).** Test `m`
genes with counts `X g` (condition 1, library size `s₁`) and `Y g` (condition 2, library size
`s₂`) by their exact conditional p-values. If each truly null gene `g ∈ H0` has independent
Poisson counts with a common rate `r g` in both conditions, then BH at level `q / H_m` has false
discovery rate at most `q |H0| / m`, however the genes depend on each other. Nothing is assumed
about the non-null genes beyond measurability. -/
theorem integral_fdp_bhRejections_countExact_le_of_arbitrary_dependence [IsProbabilityMeasure μ]
    (hs : 0 < s₁ + s₂) (X Y : Fin m → Ω → ℕ) (hXm : ∀ g, Measurable (X g))
    (hYm : ∀ g, Measurable (Y g)) (H0 : Finset (Fin m)) (r : Fin m → ℝ≥0)
    (hnull : ∀ g ∈ H0, HasLaw (X g) Po(s₁ * r g) μ ∧ HasLaw (Y g) Po(s₂ * r g) μ ∧
      IndepFun (X g) (Y g) μ)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0
        (bhRejections (q / harmonic m) fun g => countExactPValue s₁ s₂ (X g) (Y g) ω) ∂μ ≤
      q * H0.card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence μ
    (fun g => countExactPValue s₁ s₂ (X g) (Y g))
    (fun g => measurable_countExactPValue (hXm g) (hYm g)) H0
    (fun g hg => isValidPValue_countExactPValue hs (hXm g) (hYm g) (hnull g hg).1
      (hnull g hg).2.1 (hnull g hg).2.2) q hq₀ hq₁

/-- **Exact tests of independent genes (Benjamini–Hochberg).** Under the hypotheses of
`integral_fdp_bhRejections_countExact_le_of_arbitrary_dependence`, if moreover the count pairs
`(X g, Y g)` of different genes are independent, BH at level `q` itself has false discovery rate
at most `q |H0| / m`. -/
theorem integral_fdp_bhRejections_countExact_le [IsProbabilityMeasure μ]
    (hs : 0 < s₁ + s₂) (X Y : Fin m → Ω → ℕ) (hXm : ∀ g, Measurable (X g))
    (hYm : ∀ g, Measurable (Y g)) (hindep : iIndepFun (fun g ω => (X g ω, Y g ω)) μ)
    (H0 : Finset (Fin m)) (r : Fin m → ℝ≥0)
    (hnull : ∀ g ∈ H0, HasLaw (X g) Po(s₁ * r g) μ ∧ HasLaw (Y g) Po(s₂ * r g) μ ∧
      IndepFun (X g) (Y g) μ)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0
        (bhRejections q fun g => countExactPValue s₁ s₂ (X g) (Y g) ω) ∂μ ≤ q * H0.card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue μ
    (fun g => countExactPValue s₁ s₂ (X g) (Y g))
    (fun g => measurable_countExactPValue (hXm g) (hYm g))
    (hindep.comp (fun _ => countExactTail s₁ s₂) fun _ => measurable_of_countable _) H0
    (fun g hg => isValidPValue_countExactPValue hs (hXm g) (hYm g) (hnull g hg).1
      (hnull g hg).2.1 (hnull g hg).2.2) q hq₀ hq₁

end MultipleTesting

end MathlibExt.Probability.Statistics.GLM.CountData
