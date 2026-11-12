/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Simple random sampling without replacement

Under simple random sampling without replacement, every possible sample of `n`
units has the same probability of selection. Complete randomization's `randExp`
is the expectation under this design: the uniform average over all `n`-subsets.

## Main results

* `randExp_sampleMean`: the sample mean is unbiased for the population mean.
* `randExp_sq_sampleMean_sub_popMean`: the variance of the sample mean is
  `((N - n) / N) * S ^ 2 / n` with the finite population correction.

## Implementation notes

Reuses `randExp`, `sampleMean`, `popMean` and `popVar` from complete
randomization. The case `n < N` comes from Neyman's theorems with zero control
outcomes; the census case `n = N` is proved separately by direct computation.

## Not covered

Population totals, the variance estimator with `s ^ 2`, sampling with
replacement, confidence intervals, Horvitz-Thompson or inclusion-probability
definitions, causal vocabulary.

## References

Penn State STAT 506 Sampling Theory and Methods, Lesson 1, Section 1.3
"Estimating Population Mean and Total under SRS"; S. K. Thompson, Sampling,
Section 2.6, for the variance proof.
-/

@[expose] public section

namespace MathlibExt.Probability.Sampling

open MathlibExt.Probability.Causality Finset

/-- Sample mean of the zero function is zero. -/
private lemma sampleMean_zero_apply {ι : Type*} (S : Finset ι) :
    sampleMean (fun _ : ι => (0 : ℝ)) S = 0 := by
  rw [sampleMean, sum_const_zero, zero_div]

/-- With zero control outcomes, the difference in means is the sample mean. -/
private lemma diffInMeans_zero_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (S : Finset ι) :
    diffInMeans (fun _ : ι => (0 : ℝ)) y S = sampleMean y S := by
  rw [diffInMeans, sampleMean_zero_apply, sub_zero]

/-- With zero control outcomes, the average treatment effect is the mean. -/
private lemma ate_zero_left {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    ate (fun _ : ι => (0 : ℝ)) y = popMean y := by
  have hfun : (fun i : ι => y i - (0 : ℝ)) = y := funext fun _ => sub_zero _
  rw [ate, hfun]

/-- Population mean of the zero function is zero. -/
private lemma popMean_zero_apply {ι : Type*} [Fintype ι] :
    popMean (fun _ : ι => (0 : ℝ)) = 0 := by
  rw [popMean, sum_const_zero, zero_div]

/-- Population variance of the zero function is zero. -/
private lemma popVar_zero_apply {ι : Type*} [Fintype ι] :
    popVar (fun _ : ι => (0 : ℝ)) = 0 := by
  rw [popVar, popMean_zero_apply]
  simp

/-- Subtracting zero does not change the population variance. -/
private lemma popVar_sub_zero_fun {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    popVar (fun i : ι => y i - (0 : ℝ)) = popVar y := by
  have hfun : (fun i : ι => y i - (0 : ℝ)) = y := funext fun _ => sub_zero _
  rw [hfun]

/-- Sample mean over the whole population is the population mean. -/
private lemma sampleMean_univ_apply {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    sampleMean y univ = popMean y := by
  rw [sampleMean, popMean, card_univ]

/-- Census: the only `N`-subset of the population is the population. -/
private lemma powersetCard_census {ι : Type*} [Fintype ι] :
    univ.powersetCard (Fintype.card ι) = ({univ} : Finset (Finset ι)) := by
  have h := powersetCard_self (univ : Finset ι)
  rw [card_univ] at h
  exact h

/-- Census: randomization expectation at `n = N` evaluates at `univ`. -/
private lemma randExp_census_apply {ι : Type*} [Fintype ι] (f : Finset ι → ℝ) :
    randExp (Fintype.card ι) f = f univ := by
  rw [randExp, powersetCard_census, Nat.choose_self, sum_singleton]
  simp

/-- Sample-mean unbiasedness under simple random sampling without replacement.
Uses `popVar` convention only for the variance companion: `popVar` divides by
`N - 1`. Includes the census case `n = N`. -/
theorem randExp_sampleMean {ι : Type*} [Fintype ι] (y : ι → ℝ) {n : ℕ} (hn₁ : 1 ≤ n)
    (hnN : n ≤ Fintype.card ι) :
    randExp n (sampleMean y) = popMean y := by
  classical
  rcases eq_or_lt_of_le hnN with rfl | hlt
  · rw [randExp_census_apply, sampleMean_univ_apply]
  · have h₀ : n + 1 ≤ Fintype.card ι := hlt
    have hNeyman := randExp_diffInMeans (fun _ : ι => (0 : ℝ)) y hn₁ h₀
    have hfun : diffInMeans (fun _ : ι => (0 : ℝ)) y = sampleMean y :=
      funext fun S => diffInMeans_zero_left y S
    have hate : ate (fun _ : ι => (0 : ℝ)) y = popMean y := ate_zero_left y
    rw [← hfun, hNeyman, hate]

/-- Variance of the sample mean under simple random sampling without
replacement. Uses `popVar` with divisor `N - 1`. Includes the census case
`n = N`, where both sides are zero. -/
theorem randExp_sq_sampleMean_sub_popMean {ι : Type*} [Fintype ι] (y : ι → ℝ) {n : ℕ}
    (hn₁ : 1 ≤ n) (hnN : n ≤ Fintype.card ι) :
    randExp n (fun S => (sampleMean y S - popMean y) ^ 2) =
      (1 - (n : ℝ) / Fintype.card ι) * popVar y / n := by
  classical
  rcases eq_or_lt_of_le hnN with rfl | hlt
  · have hNpos : (0 : ℝ) < Fintype.card ι := by
      have h1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn₁
      linarith
    have hNne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hNpos
    have hmean : sampleMean y univ = popMean y := sampleMean_univ_apply y
    have hdiv : (Fintype.card ι : ℝ) / Fintype.card ι = 1 := div_self hNne
    rw [randExp_census_apply, hmean, sub_self, zero_pow (by norm_num : 2 ≠ 0)]
    rw [hdiv, sub_self, zero_mul, zero_div]
  · have h₀ : n + 1 ≤ Fintype.card ι := hlt
    have hNeyman :=
      randExp_sq_diffInMeans_sub_ate (fun _ : ι => (0 : ℝ)) y hn₁ h₀
    have hfun : (fun S : Finset ι =>
          (diffInMeans (fun _ : ι => (0 : ℝ)) y S -
            ate (fun _ : ι => (0 : ℝ)) y) ^ 2) =
        (fun S : Finset ι => (sampleMean y S - popMean y) ^ 2) := by
      funext S
      rw [diffInMeans_zero_left, ate_zero_left]
    have hz : popVar (fun _ : ι => (0 : ℝ)) = 0 := popVar_zero_apply
    have hsub : popVar (fun i : ι => y i - (fun _ : ι => (0 : ℝ)) i) =
        popVar y :=
      popVar_sub_zero_fun y
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hN0 : (Fintype.card ι : ℝ) ≠ 0 := by
      have h1 : (1 : ℝ) ≤ Fintype.card ι := by
        have : 1 ≤ Fintype.card ι := hn₁.trans hnN
        exact_mod_cast this
      linarith
    rw [← hfun, hNeyman, hz, hsub]
    simp only [zero_div, add_zero]
    field_simp

end MathlibExt.Probability.Sampling
