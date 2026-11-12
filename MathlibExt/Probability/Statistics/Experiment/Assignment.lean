/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Moments.Variance

/-!
# The complete-randomization assignment law

A finite population `ι` of `N` units with fixed potential outcomes `y₀ y₁ : ι → ℝ` is assigned
to treatment by *complete randomization*: the treated set is uniform among the `(N choose n₁)`
subsets of size `n₁`. This file realizes that design as a probability measure on `Finset ι` and
restates Neyman's (1923) finite-population results, proved in
`MathlibExt/Probability/Causality/CausalIdentification.lean` for the uniform average `randExp`,
as integrals and variances under the law.

## Main definitions

* `completeRandomization ι n₁`: the uniform measure `Measure.uniformOfFinset` on the treated sets
  of size `n₁`; a probability measure for `n₁ ≤ N` and the zero measure for `n₁ > N`.

## Main results

* `isProbabilityMeasure_completeRandomization` and `integral_completeRandomization`: for
  `n₁ ≤ N` the law is normalized, and integrating a statistic against it is `randExp`.
* With both arms nonempty (`1 ≤ n₁`, `n₁ + 1 ≤ N`):
  `integral_diffInMeans_completeRandomization` (the difference in means is unbiased for the
  average treatment effect), `integral_sq_diffInMeans_sub_ate_completeRandomization` and
  `variance_diffInMeans_completeRandomization` (its variance is `S₁²/n₁ + S₀²/n₀ - S_τ²/N`).
* With both arms of size at least two (`2 ≤ n₁`, `n₁ + 2 ≤ N`):
  `integral_neymanVar_completeRandomization` (Neyman's estimator has expectation
  `S₁²/n₁ + S₀²/n₀`), and `integral_sq_diffInMeans_sub_ate_le_integral_neymanVar` and
  `variance_diffInMeans_le_integral_neymanVar` (it is conservative, with equality exactly for a
  constant treatment effect).

## Not covered

Fisher randomization tests under the sharp null, identification assumptions, blocked and
factorial designs, and superpopulation (asymptotic) versions.

## References

* J. Neyman, *On the application of probability theory to agricultural experiments* (1923);
  translated by D. M. Dabrowska and T. P. Speed, Statistical Science 5(4) (1990), 465–472.
* G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
  Sciences*, Cambridge University Press (2015), Chapter 6.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Experiment

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Causality

/-- Complete randomization of `n₁` treated units among the finite population `ι`: the uniform
measure on the treated sets of size `n₁`. It is a probability measure when `n₁ ≤ |ι|` and the
zero measure when `n₁ > |ι|`. -/
noncomputable def completeRandomization (ι : Type*) [Fintype ι] (n₁ : ℕ) :
    Measure (Finset ι) :=
  Measure.uniformOfFinset (univ.powersetCard n₁ : Finset (Finset ι))

theorem completeRandomization_eq (ι : Type*) [Fintype ι] (n₁ : ℕ) :
    completeRandomization ι n₁ =
      Measure.uniformOfFinset (univ.powersetCard n₁ : Finset (Finset ι)) := by
  rfl

theorem isProbabilityMeasure_completeRandomization {ι : Type*} [Fintype ι] {n₁ : ℕ}
    (h : n₁ ≤ Fintype.card ι) :
    IsProbabilityMeasure (completeRandomization ι n₁) := by
  constructor
  have hC : ((univ.powersetCard n₁ : Finset (Finset ι)).card : ENNReal) ≠ 0 := by
    rw [card_powersetCard, card_univ]
    exact_mod_cast (Nat.choose_pos h).ne'
  rw [completeRandomization_eq, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, filter_true]
  exact ENNReal.div_self hC (ENNReal.natCast_ne_top _)

/-- Integrals against the complete-randomization law are the existing uniform averages
`randExp`, for `n₁ ≤ |ι|`. -/
theorem integral_completeRandomization {ι : Type*} [Fintype ι] {n₁ : ℕ}
    (h : n₁ ≤ Fintype.card ι) (f : Finset ι → ℝ) :
    ∫ S, f S ∂(completeRandomization ι n₁) = randExp n₁ f := by
  have hC : ((univ.powersetCard n₁ : Finset (Finset ι)).card : ENNReal) ≠ 0 := by
    rw [card_powersetCard, card_univ]
    exact_mod_cast (Nat.choose_pos h).ne'
  rw [completeRandomization_eq, Measure.uniformOfFinset,
    integral_finsetSum_measure fun S _ =>
      (Integrable.of_finite : Integrable f (Measure.dirac S)).smul_measure
        (ENNReal.inv_ne_top.2 hC)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← mul_sum, card_powersetCard, card_univ, randExp]
  ring

/-- Neyman (1923), law form: the difference in means is unbiased for the ATE. -/
theorem integral_diffInMeans_completeRandomization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 1 ≤ n₁) (h₀ : n₁ + 1 ≤ Fintype.card ι) :
    ∫ S, diffInMeans y₀ y₁ S ∂(completeRandomization ι n₁) = ate y₀ y₁ := by
  rw [integral_completeRandomization (by omega)]
  exact randExp_diffInMeans y₀ y₁ h₁ h₀

/-- Neyman (1923), law form: exact mean squared error `S₁²/n₁ + S₀²/n₀ - S_τ²/N`. -/
theorem integral_sq_diffInMeans_sub_ate_completeRandomization {ι : Type*} [Fintype ι]
    [DecidableEq ι] (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 1 ≤ n₁) (h₀ : n₁ + 1 ≤ Fintype.card ι) :
    ∫ S, (diffInMeans y₀ y₁ S - ate y₀ y₁) ^ 2 ∂(completeRandomization ι n₁) =
      popVar y₁ / n₁ + popVar y₀ / ((Fintype.card ι : ℝ) - n₁) -
        popVar (fun i => y₁ i - y₀ i) / Fintype.card ι := by
  rw [integral_completeRandomization (by omega)]
  exact randExp_sq_diffInMeans_sub_ate y₀ y₁ h₁ h₀

/-- Neyman (1923), law form: the variance of the difference in means under complete
randomization. -/
theorem variance_diffInMeans_completeRandomization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 1 ≤ n₁) (h₀ : n₁ + 1 ≤ Fintype.card ι) :
    variance (diffInMeans y₀ y₁) (completeRandomization ι n₁) =
      popVar y₁ / n₁ + popVar y₀ / ((Fintype.card ι : ℝ) - n₁) -
        popVar (fun i => y₁ i - y₀ i) / Fintype.card ι := by
  rw [variance_eq_integral Measurable.of_discrete.aemeasurable,
    integral_diffInMeans_completeRandomization y₀ y₁ h₁ h₀]
  exact integral_sq_diffInMeans_sub_ate_completeRandomization y₀ y₁ h₁ h₀

/-- Law form of the expectation of Neyman's variance estimator (both arms of size `≥ 2`). -/
theorem integral_neymanVar_completeRandomization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 2 ≤ n₁) (h₀ : n₁ + 2 ≤ Fintype.card ι) :
    ∫ S, neymanVar y₀ y₁ S ∂(completeRandomization ι n₁) =
      popVar y₁ / n₁ + popVar y₀ / ((Fintype.card ι : ℝ) - n₁) := by
  rw [integral_completeRandomization (by omega)]
  exact randExp_neymanVar y₀ y₁ h₁ h₀

/-- Law form: Neyman's estimator is conservative, with equality exactly for a constant
treatment effect (both arms of size `≥ 2`). -/
theorem integral_sq_diffInMeans_sub_ate_le_integral_neymanVar {ι : Type*} [Fintype ι]
    [DecidableEq ι] (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 2 ≤ n₁) (h₀ : n₁ + 2 ≤ Fintype.card ι) :
    ∫ S, (diffInMeans y₀ y₁ S - ate y₀ y₁) ^ 2 ∂(completeRandomization ι n₁) ≤
        ∫ S, neymanVar y₀ y₁ S ∂(completeRandomization ι n₁) ∧
      (∫ S, (diffInMeans y₀ y₁ S - ate y₀ y₁) ^ 2 ∂(completeRandomization ι n₁) =
          ∫ S, neymanVar y₀ y₁ S ∂(completeRandomization ι n₁) ↔
        ∃ c, ∀ i, y₁ i - y₀ i = c) := by
  rw [integral_completeRandomization (by omega), integral_completeRandomization (by omega)]
  exact randVar_le_randExp_neymanVar y₀ y₁ h₁ h₀

/-- Variance form of the conservativeness of Neyman's estimator. -/
theorem variance_diffInMeans_le_integral_neymanVar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 2 ≤ n₁) (h₀ : n₁ + 2 ≤ Fintype.card ι) :
    variance (diffInMeans y₀ y₁) (completeRandomization ι n₁) ≤
        ∫ S, neymanVar y₀ y₁ S ∂(completeRandomization ι n₁) ∧
      (variance (diffInMeans y₀ y₁) (completeRandomization ι n₁) =
          ∫ S, neymanVar y₀ y₁ S ∂(completeRandomization ι n₁) ↔
        ∃ c, ∀ i, y₁ i - y₀ i = c) := by
  rw [variance_diffInMeans_completeRandomization y₀ y₁ (by omega) (by omega),
    ← integral_sq_diffInMeans_sub_ate_completeRandomization y₀ y₁ (by omega) (by omega)]
  exact integral_sq_diffInMeans_sub_ate_le_integral_neymanVar y₀ y₁ h₁ h₀

end MathlibExt.Probability.Statistics.Experiment
