/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability

/-!
# Tests for finite probability, moments and least squares

* A two-state (Bernoulli) distribution with explicit mean and variance.
* Total probability with explicit weights on `Fin 6`: an event split along a second event, and
  a partition of `Fin 6` into three events.
* Uncorrelated but dependent variables on `Fin 3`: joint probability `1 / 3`, product `1 / 9`.
* A full-rank calibration line through three non-collinear points, with exact slope and
  intercept, residuals summing to zero and orthogonal to `x`.
* A constant regressor, where `S_xx = 0` and the least-squares line is not unique.
* A partition-function (Gibbs) expectation and a normal-location coverage statement.
* A posterior credible interval, a realized pivot interval that misses the parameter, Bessel's
  correction, a covariance-matrix identity and the comparison with `PMF`.
-/

@[expose] public section

open Finset Matrix MeasureTheory MathlibExt.Probability.FiniteProbability

namespace MathlibExtTest.Probability.FiniteProbability

/-! ### Two-state distribution -/

/-- The weight `(3 / 4, 1 / 4)` on `Fin 2` is a finite distribution. -/
example : (∀ i, 0 ≤ (![3 / 4, 1 / 4] : Fin 2 → ℝ) i) ∧
    ∑ i, (![3 / 4, 1 / 4] : Fin 2 → ℝ) i = 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num
  · simp only [Fin.sum_univ_two]
    norm_num

/-- Under `(3 / 4, 1 / 4)` the indicator `(0, 1)` has mean `1 / 4`. -/
example : expectation ![3 / 4, 1 / 4] ![0, 1] = 1 / 4 := by
  rw [show (![3 / 4, 1 / 4] : Fin 2 → ℝ) = ![1 - 1 / 4, 1 / 4] by norm_num,
    expectation_two_state]

/-- Under `(3 / 4, 1 / 4)` the indicator `(0, 1)` has variance `3 / 16`. -/
example : variance ![3 / 4, 1 / 4] ![0, 1] = 3 / 16 := by
  rw [show (![3 / 4, 1 / 4] : Fin 2 → ℝ) = ![1 - 1 / 4, 1 / 4] by norm_num,
    variance_two_state]
  norm_num

/-- The same variance by direct computation from the definition. -/
example : variance ![3 / 4, 1 / 4] ![0, 1] = 3 / 16 := by
  simp only [variance, expectation, Fin.sum_univ_two]
  norm_num

/-! ### Total probability -/

/-- Weights `(1 / 12, 1 / 6, 1 / 4, 1 / 12, 1 / 4, 1 / 6)` on `Fin 6`. -/
noncomputable def partP : Fin 6 → ℝ := ![1 / 12, 1 / 6, 1 / 4, 1 / 12, 1 / 4, 1 / 6]

/-- The labels `(0, 0, 1, 1, 2, 2)`, whose fibres `{0, 1}`, `{2, 3}` and `{4, 5}` partition
`Fin 6` into three events. -/
def partF : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

private lemma sum_partP : ∑ i, partP i = 1 := by
  simp only [partP, Fin.sum_univ_six]
  norm_num

private lemma prob_partF : prob partP (univ.filter fun x => partF x = 0) = 1 / 4 ∧
    prob partP (univ.filter fun x => partF x = 1) = 1 / 3 ∧
    prob partP (univ.filter fun x => partF x = 2) = 5 / 12 := by
  rw [show (univ.filter fun x => partF x = 0) = {0, 1} by decide,
    show (univ.filter fun x => partF x = 1) = {2, 3} by decide,
    show (univ.filter fun x => partF x = 2) = {4, 5} by decide]
  norm_num [prob, partP]

/-- Two-set total probability: `s = {0, 2, 4}` splits along `t = {0, 1, 2}` into
`s ∩ t = {0, 2}` and `s \ t = {4}`, so `P(s) = 1 / 3 + 1 / 4 = 7 / 12`. -/
example : prob partP {0, 2, 4} = 7 / 12 := by
  rw [← prob_inter_add_prob_sdiff partP {0, 2, 4} {0, 1, 2},
    show ({0, 2, 4} ∩ {0, 1, 2} : Finset (Fin 6)) = {0, 2} by decide,
    show ({0, 2, 4} \ {0, 1, 2} : Finset (Fin 6)) = {4} by decide]
  norm_num [prob, partP]

/-- Law of total probability for the 3-part partition by `partF`: the probabilities of the
three events sum to `P(Fin 6) = 1`. -/
example : ∑ i, prob partP (univ.filter fun x => partF x = i) = 1 := by
  rw [sum_prob_filter_eq, prob_univ sum_partP]

/-- The same law determines the probability of the third event from the other two,
`1 - 1 / 4 - 1 / 3 = 5 / 12`, which `prob_partF` also computes directly. -/
example : prob partP (univ.filter fun x => partF x = 2) = 5 / 12 := by
  have h := sum_prob_filter_eq partP partF univ
  rw [Fin.sum_univ_three, prob_univ sum_partP, prob_partF.1, prob_partF.2.1] at h
  linarith

/-! ### Zero covariance without independence -/

/-- Under the uniform weight on `Fin 3`, `X = (-1, 0, 1)` and `Y = X ^ 2` are uncorrelated. -/
example : covariance (fun _ : Fin 3 => (1 / 3 : ℝ)) ![-1, 0, 1]
    (fun i => ![(-1 : ℝ), 0, 1] i ^ 2) = 0 := by
  simp only [covariance, expectation, Fin.sum_univ_three]
  norm_num

/-- The event `{X = 0, Y = 0}` has probability `1 / 3`. -/
example : prob (fun _ : Fin 3 => (1 / 3 : ℝ))
    (univ.filter fun i => ![(-1 : ℝ), 0, 1] i = 0 ∧ ![(-1 : ℝ), 0, 1] i ^ 2 = 0) = 1 / 3 := by
  simp only [prob, Finset.sum_filter, Fin.sum_univ_three]
  norm_num

/-- The probabilities of `{X = 0}` and `{Y = 0}` multiply to `1 / 9 ≠ 1 / 3`. -/
example : prob (fun _ : Fin 3 => (1 / 3 : ℝ)) (univ.filter fun i => ![(-1 : ℝ), 0, 1] i = 0) *
    prob (fun _ : Fin 3 => (1 / 3 : ℝ)) (univ.filter fun i => ![(-1 : ℝ), 0, 1] i ^ 2 = 0) =
      1 / 9 := by
  simp only [prob, Finset.sum_filter, Fin.sum_univ_three]
  norm_num

/-- The packaged counterexample. -/
example : ∃ p X : Fin 3 → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
    covariance p X (fun i => X i ^ 2) = 0 ∧
    prob p (univ.filter fun i => X i = 0 ∧ X i ^ 2 = 0) ≠
      prob p (univ.filter fun i => X i = 0) * prob p (univ.filter fun i => X i ^ 2 = 0) :=
  exists_covariance_eq_zero_prob_ne

/-- Two independent fair bits: product events factor and the coordinates are uncorrelated. -/
example : prob (fun z : Fin 2 × Fin 2 => (![1 / 2, 1 / 2] : Fin 2 → ℝ) z.1 *
      (![1 / 2, 1 / 2] : Fin 2 → ℝ) z.2) ({1} ×ˢ {1}) = 1 / 4 ∧
    covariance (fun z : Fin 2 × Fin 2 => (![1 / 2, 1 / 2] : Fin 2 → ℝ) z.1 *
      (![1 / 2, 1 / 2] : Fin 2 → ℝ) z.2) (fun z => (![0, 1] : Fin 2 → ℝ) z.1)
      (fun z => (![0, 1] : Fin 2 → ℝ) z.2) = 0 := by
  have h : ∑ i, (![1 / 2, 1 / 2] : Fin 2 → ℝ) i = 1 := by
    simp only [Fin.sum_univ_two]
    norm_num
  refine ⟨?_, covariance_prod_eq_zero h h _ _⟩
  rw [prob_prod]
  simp only [prob, Finset.sum_singleton]
  norm_num

/-! ### Full-rank calibration line -/

/-- Calibration inputs `x = (0, 1, 2)`. -/
noncomputable def calX : Fin 3 → ℝ := ![0, 1, 2]

/-- Calibration responses `y = (1, 2, 4)`; the points `(0, 1), (1, 2), (2, 4)` are not
collinear. -/
noncomputable def calY : Fin 3 → ℝ := ![1, 2, 4]

private lemma sxx_cal : sxy calX calX = 2 := by
  simp only [sxy, sampleMean_eq_sum_div, calX, Fin.sum_univ_three, Fintype.card_fin]
  norm_num

private lemma sxy_cal : sxy calX calY = 3 := by
  simp only [sxy, sampleMean_eq_sum_div, calX, calY, Fin.sum_univ_three, Fintype.card_fin]
  norm_num

private lemma slope_cal : olsSlope calX calY = 3 / 2 := by
  rw [olsSlope, sxy_cal, sxx_cal]

private lemma intercept_cal : olsIntercept calX calY = 5 / 6 := by
  rw [olsIntercept, slope_cal]
  simp only [sampleMean_eq_sum_div, calX, calY, Fin.sum_univ_three, Fintype.card_fin]
  norm_num

/-- The sample means are `x̄ = 1` and `ȳ = 7 / 3`. -/
example : sampleMean calX = 1 ∧ sampleMean calY = 7 / 3 := by
  constructor <;>
    simp only [sampleMean_eq_sum_div, calX, calY, Fin.sum_univ_three, Fintype.card_fin] <;>
    norm_num

/-- `S_xx = 2 > 0`. -/
example : 0 < sxy calX calX := by
  rw [sxx_cal]
  norm_num

/-- The exact least-squares line is `5 / 6 + 3 / 2 x`. -/
example : olsSlope calX calY = 3 / 2 ∧ olsIntercept calX calY = 5 / 6 :=
  ⟨slope_cal, intercept_cal⟩

/-- The residuals `(1 / 6, -1 / 3, 1 / 6)` sum to zero. -/
example : ∑ i, (calY i - (olsIntercept calX calY + olsSlope calX calY * calX i)) = 0 := by
  rw [intercept_cal, slope_cal]
  simp only [calX, calY, Fin.sum_univ_three]
  norm_num

/-- The residuals are orthogonal to `x`. -/
example : ∑ i, calX i * (calY i - (olsIntercept calX calY + olsSlope calX calY * calX i)) =
    0 := by
  rw [intercept_cal, slope_cal]
  simp only [calX, calY, Fin.sum_univ_three]
  norm_num

/-- The same two facts from the general lemmas. -/
example : ∑ i, (calY i - (olsIntercept calX calY + olsSlope calX calY * calX i)) = 0 ∧
    ∑ i, calX i * (calY i - (olsIntercept calX calY + olsSlope calX calY * calX i)) = 0 :=
  ⟨sum_resid_ols _ _, sum_mul_resid_ols _ _⟩

/-- The minimal residual sum of squares is `1 / 6 > 0`, so no line fits all three points. -/
example : rssLine calX calY (olsIntercept calX calY) (olsSlope calX calY) = 1 / 6 ∧
    ∀ a b, 0 < rssLine calX calY a b := by
  have h : rssLine calX calY (olsIntercept calX calY) (olsSlope calX calY) = 1 / 6 := by
    rw [intercept_cal, slope_cal]
    simp only [rssLine, calX, calY, Fin.sum_univ_three]
    norm_num
  refine ⟨h, fun a b => ?_⟩
  have := rssLine_ols_le calX calY a b
  rw [h] at this
  linarith

/-- `(5 / 6, 3 / 2)` is the unique minimizer of the residual sum of squares. -/
example (a b : ℝ) (h : rssLine calX calY a b ≤ rssLine calX calY (5 / 6) (3 / 2)) :
    a = 5 / 6 ∧ b = 3 / 2 := by
  have hpos : 0 < sxy calX calX := by
    rw [sxx_cal]
    norm_num
  have := ((ols_unique_minimizer_iff calX calY).mpr hpos a b).2
  rw [intercept_cal, slope_cal] at this
  exact this h

/-- The design matrix with rows `(1, x i)` has full column rank. -/
example : IsUnit ((designMatrix calX)ᵀ * designMatrix calX) := by
  rw [isUnit_gram_designMatrix_iff, sxx_cal]
  norm_num

/-- The matrix least-squares estimator for the design matrix is `(5 / 6, 3 / 2)`. -/
example : MathlibExt.Probability.Statistics.LinearModel.olsEstimator (designMatrix calX) calY =
    ![5 / 6, 3 / 2] := by
  rw [olsEstimator_designMatrix (by rw [sxx_cal]; norm_num), intercept_cal, slope_cal]

/-! ### Constant regressor: `S_xx = 0` -/

/-- A constant regressor `x = (1, 1, 1)`. -/
noncomputable def constX : Fin 3 → ℝ := ![1, 1, 1]

/-- Responses `y = (1, 2, 3)` for the constant regressor. -/
noncomputable def constY : Fin 3 → ℝ := ![1, 2, 3]

private lemma sxx_const : sxy constX constX = 0 := by
  simp only [sxy, sampleMean_eq_sum_div, constX, Fin.sum_univ_three, Fintype.card_fin]
  norm_num

/-- Two different lines, `2 + 0 x` and `1 + 1 x`, have the same residual sum of squares `2`. -/
example : rssLine constX constY 2 0 = 2 ∧ rssLine constX constY 1 1 = 2 := by
  constructor <;> simp only [rssLine, constX, constY, Fin.sum_univ_three] <;> norm_num

/-- Both lines are minimizers, so the minimizer is not unique. -/
example (a b : ℝ) : rssLine constX constY 2 0 ≤ rssLine constX constY a b ∧
    rssLine constX constY 1 1 ≤ rssLine constX constY a b := by
  have hI : olsIntercept constX constY = 2 := by
    rw [olsIntercept, olsSlope, sxx_const, div_zero, zero_mul, sub_zero]
    simp only [sampleMean_eq_sum_div, constY, Fin.sum_univ_three, Fintype.card_fin]
    norm_num
  have hS : olsSlope constX constY = 0 := by rw [olsSlope, sxx_const, div_zero]
  have h := rssLine_ols_le constX constY a b
  rw [hI, hS] at h
  refine ⟨h, ?_⟩
  have hshift := rssLine_shift_eq_of_sxy_self_eq_zero sxx_const constY 2 0 1
  have hm : sampleMean constX = 1 := by
    simp only [sampleMean_eq_sum_div, constX, Fin.sum_univ_three, Fintype.card_fin]
    norm_num
  rw [hm] at hshift
  norm_num at hshift
  rw [hshift]
  exact h

/-- Hence uniqueness fails, as `ols_unique_minimizer_iff` requires `0 < S_xx`. -/
example : ¬ ∀ a b, rssLine constX constY (olsIntercept constX constY) (olsSlope constX constY) ≤
      rssLine constX constY a b ∧
    (rssLine constX constY a b ≤ rssLine constX constY (olsIntercept constX constY)
        (olsSlope constX constY) →
      a = olsIntercept constX constY ∧ b = olsSlope constX constY) := by
  rw [ols_unique_minimizer_iff, sxx_const]
  exact lt_irrefl 0

/-- The design matrix of a constant regressor does not have full column rank. -/
example : ¬ IsUnit ((designMatrix constX)ᵀ * designMatrix constX) := by
  rw [isUnit_gram_designMatrix_iff, sxx_const]
  exact lt_irrefl 0

/-! ### Partition function and the normal location model -/

/-- A two-level system with energies `0` and `1` at inverse temperature `β`: the Gibbs weights
`exp (-β E) / Z` sum to `1`. -/
example (β : ℝ) :
    ∑ i, Real.exp (-β * (![0, 1] : Fin 2 → ℝ) i) /
      ∑ j, Real.exp (-β * (![0, 1] : Fin 2 → ℝ) j) = 1 :=
  sum_div_sum_eq_one (by positivity)

/-- The mean energy of the two-level system is `exp (-β) / (1 + exp (-β))`. -/
example (β : ℝ) :
    expectation (fun i => Real.exp (-β * (![0, 1] : Fin 2 → ℝ) i) /
      ∑ j, Real.exp (-β * (![0, 1] : Fin 2 → ℝ) j)) ![0, 1] =
        Real.exp (-β) / (1 + Real.exp (-β)) := by
  rw [expectation_div_sum]
  simp [Fin.sum_univ_two]

/-- Under `N(θ, 1)` on `ℝ` the identity statistic has a standard normal pivot, so `[t - z, t + z]`
contains `θ` with probability `N(0, 1) [-z, z]`; here the pivot law is derived, not assumed. -/
example (θ z : ℝ) :
    ProbabilityTheory.gaussianReal θ 1 {t | θ ∈ pivotInterval t 1 (-z) z} =
      ProbabilityTheory.gaussianReal 0 1 (Set.Icc (-z) z) := by
  have hpivot := hasLaw_pivot_of_hasLaw_gaussianReal (T := id) one_ne_zero (by simp)
    (ProbabilityTheory.HasLaw.id (μ := ProbabilityTheory.gaussianReal θ 1))
  exact measure_mem_pivotInterval one_pos hpivot

/-- The known-variance normal location model with `n = 4` and `σ = 2`, under its pivot
hypothesis. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ z : ℝ) (X : Ω → Fin 4 → ℝ)
    (hpivot : ProbabilityTheory.HasLaw (fun ω => (sampleMean (X ω) - θ) / (2 / √4))
      (ProbabilityTheory.gaussianReal 0 1) μ) :
    μ {ω | θ ∈ Set.Icc (sampleMean (X ω) - z * (2 / √4)) (sampleMean (X ω) + z * (2 / √4))} =
      ProbabilityTheory.gaussianReal 0 1 (Set.Icc (-z) z) :=
  measure_mem_zInterval (by norm_num) (by norm_num) hpivot z

/-- A realized interval need not contain the parameter: `0 ∉ [10 - 2, 10 + 2]`. -/
example : (0 : ℝ) ∉ pivotInterval 10 1 (-2) 2 := by
  simp only [pivotInterval, Set.mem_Icc, not_and, not_le]
  intro h
  norm_num at h

/-! ### Credible intervals, sample statistics and covariance matrices -/

/-- Bias `θ ∈ {1 / 4, 1 / 2, 3 / 4}`, uniform prior and one observed head: the posterior is
`θ / ∑ θ = (1 / 6, 1 / 3, 1 / 2)`, and `[1 / 2, 1]` is a level-`5 / 6` credible interval. -/
example : IsCredibleInterval
    (fun t => (![1 / 4, 1 / 2, 3 / 4] : Fin 3 → ℝ) t / ∑ s, (![1 / 4, 1 / 2, 3 / 4] : Fin 3 → ℝ) s)
    ![1 / 4, 1 / 2, 3 / 4] (1 / 2) 1 (5 / 6) := by
  refine ⟨fun t => ?_, sum_div_sum_eq_one (by simp only [Fin.sum_univ_three]; norm_num), ?_⟩
  · simp only [Fin.sum_univ_three]
    fin_cases t <;> norm_num
  · simp only [prob, Finset.sum_filter, Fin.sum_univ_three, Set.mem_Icc]
    norm_num

/-- The posterior coverage identity for a credible interval. -/
example {Θ : Type*} [Fintype Θ] (post θ : Θ → ℝ) (lo hi c : ℝ)
    (h : IsCredibleInterval post θ lo hi c) :
    expectation post (fun t => if θ t ∈ Set.Icc lo hi then 1 else 0) = c :=
  h.expectation_indicator_eq

/-- Sample statistics of `(0, 1, 2)`: variances `2 / 3` (divide by `n`) and `1` (by `n - 1`). -/
example : sampleVar calX = 2 / 3 ∧ sampleVarUnbiased calX = 1 := by
  constructor <;>
    simp only [sampleVar, sampleVarUnbiased_eq_sum_div, sampleMean_eq_sum_div, calX,
      Fin.sum_univ_three, Fintype.card_fin] <;>
    norm_num

/-- Bessel's correction for two fair-bit draws: `E[s²] = Var X = 1 / 4`. -/
example : expectation (fun ω : Fin 2 → Fin 2 => ∏ i, (![1 / 2, 1 / 2] : Fin 2 → ℝ) (ω i))
    (fun ω => sampleVarUnbiased fun i => (![0, 1] : Fin 2 → ℝ) (ω i)) = 1 / 4 := by
  rw [expectation_sampleVarUnbiased (by simp only [Fin.sum_univ_two]; norm_num) (by simp)]
  simp only [variance, expectation, Fin.sum_univ_two]
  norm_num

/-- `Var (X₀ + X₁) = Var X₀ + 2 Cov (X₀, X₁) + Var X₁`, from `covMatrix_mulVec`. -/
example {α : Type*} [Fintype α] (p : α → ℝ) (X : α → Fin 2 → ℝ) :
    covMatrix p (fun x => !![(1 : ℝ), 1] *ᵥ X x) 0 0 =
      covMatrix p X 0 0 + 2 * covMatrix p X 0 1 + covMatrix p X 1 1 := by
  have hsym : covMatrix p X 1 0 = covMatrix p X 0 1 := covariance_comm _ _ _
  rw [covMatrix_mulVec]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hsym]
  ring

/-- For a `PMF`, Mathlib's variance against `q.toMeasure` is the finite-sum variance, and the
weights `(q a).toReal` form a finite distribution. -/
example (q : PMF (Fin 3)) (X : Fin 3 → ℝ) :
    ProbabilityTheory.variance X q.toMeasure = variance (fun a => (q a).toReal) X ∧
      ∑ a, (q a).toReal = 1 :=
  ⟨variance_toMeasure_eq q X, sum_toReal_eq_one q⟩

end MathlibExtTest.Probability.FiniteProbability
