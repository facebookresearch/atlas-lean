/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCount

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped Nat
open MathlibExt.Biology.Omics.HierarchicalCount

namespace MathlibExtTest.Biology.Omics.HierarchicalCount

/-- At size factor `s = 1` the likelihood is the unit-rate Poisson mass used by
`poissonMixtureReal`, so the marginal likelihood is the existing Poisson–Gamma mixture. -/
example (a b : ℝ) (k : ℕ) :
    marginalLik a b 1 k = poissonMixtureReal (gammaMeasure a b) k := by
  simp [marginalLik, poissonExposureLik, poissonMixtureReal]

/-- At `s = 1` the exposure conjugacy agrees with the existing
`ProbabilityTheory.gammaPDFReal_posterior`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) (r : ℝ) :
    poissonExposureLik 1 k r * gammaPDFReal a b r / marginalLik a b 1 k =
      exp (-r) * r ^ k / k ! * gammaPDFReal a b r / poissonMixtureReal (gammaMeasure a b) k := by
  rw [posterior_eq_gammaPDFReal ha hb one_pos, gammaPDFReal_posterior ha hb]

/-- Conjugacy at a concrete size factor `s = 2`: prior `Gamma(3, 1)`, count `4`, posterior
`Gamma(7, 3)`. -/
example (r : ℝ) :
    poissonExposureLik 2 4 r * gammaPDFReal 3 1 r / marginalLik 3 1 2 4 =
      gammaPDFReal 7 3 r := by
  have h := posterior_eq_gammaPDFReal (a := 3) (b := 1) (s := 2) (by norm_num) (by norm_num)
    (by norm_num) 4 r
  norm_num at h
  exact h

/-- The marginal law at `a = 2`, `b = 1`, `s = 1` is `NB(2, 2)`, whose zero mass is `1 / 4`. -/
example : marginalLik 2 1 1 0 = 1 / 4 := by
  rw [marginalLik_eq_negBinomialReal (by norm_num) (by norm_num) (by norm_num)]
  norm_num [negBinomialReal, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]

/-- Concrete shrinkage: prior `Gamma(2, 1)` (mean `2`), `s = 1`, count `3`. The weight is
`1 / 2` and the posterior mean `5 / 2` is the midpoint of `3` and `2`. -/
example : shrinkageWeight 1 1 = 1 / 2 ∧ posteriorMean 2 1 1 3 = 5 / 2 ∧
    posteriorMean 2 1 1 3 =
      shrinkageWeight 1 1 * (3 / 1) + (1 - shrinkageWeight 1 1) * (2 / 1) := by
  refine ⟨by norm_num [shrinkageWeight], by norm_num [posteriorMean], ?_⟩
  exact_mod_cast posteriorMean_eq_shrinkage (a := 2) (b := 1) (s := 1) one_pos one_pos 3

/-- The posterior mean is a genuine compromise: for count `3` and prior mean `2` it lies in
`[2, 3]`. -/
example : posteriorMean 2 1 1 3 ∈ segment ℝ (2 / 1) (3 / 1) := by
  exact_mod_cast posteriorMean_mem_segment (a := 2) (b := 1) (s := 1) one_pos one_pos 3

/-- **Zero count.** Prior `Gamma(2, 1)`, `s = 1`, count `0`: posterior mean `1`, strictly
between `0` and the prior mean `2`. -/
example : posteriorMean 2 1 1 0 = 1 ∧ posteriorMean 2 1 1 0 ∈ Set.Ioo 0 (2 / 1) :=
  ⟨by norm_num [posteriorMean],
    posteriorMean_zero_mem_Ioo (a := 2) (b := 1) (s := 1) (by norm_num) one_pos one_pos⟩

/-- **No-shrinkage limit at a zero count.** As the prior variance grows, the posterior mean of a
zero count tends to `0 / s = 0`: shrinkage is what keeps it positive. -/
example (m : ℝ) :
    Tendsto (fun v => posteriorMean (m ^ 2 / v) (m / v) 2 0) atTop (𝓝 0) := by
  simpa using tendsto_posteriorMean_priorVariance_atTop m (s := 2) two_pos 0

/-- The shrinkage weight tends to `1` as the prior rate tends to `0⁺`, at `s = 3`. -/
example : Tendsto (fun b => shrinkageWeight b 3) (𝓝[>] 0) (𝓝 1) :=
  tendsto_shrinkageWeight_zero (by norm_num)

/-- **Full shrinkage.** With prior mean `5` and vanishing prior variance, the posterior mean of
any count tends to `5`. -/
example (k : ℕ) :
    Tendsto (fun v => posteriorMean (5 ^ 2 / v) (5 / v) 1 k) (𝓝[>] 0) (𝓝 5) :=
  tendsto_posteriorMean_priorVariance_zero (by norm_num) zero_le_one k

/-- Concrete moment estimates: mean `2`, variance `6`, `s = 1` give `â = 1`, `b̂ = 1 / 2`, which
solve the moment equations `s â / b̂ = 2`, `2 + 2² / â = 6`. -/
example : momShape 2 6 = 1 ∧ momRate 1 2 6 = 1 / 2 ∧
    1 * momShape 2 6 / momRate 1 2 6 = 2 ∧ 2 + 2 ^ 2 / momShape 2 6 = 6 :=
  ⟨by norm_num [momShape], by norm_num [momRate],
    mom_moment_equations (by norm_num) (by norm_num) (by norm_num)⟩

/-- The empirical-Bayes posterior mean at those estimates for count `3`:
`(1 + 3) / (1 / 2 + 1) = 8 / 3`. -/
example : ebPosteriorMean 1 2 6 3 = 8 / 3 := by
  norm_num [ebPosteriorMean, posteriorMean, momShape, momRate]

/-- Fisher consistency at `a = 2`, `b = 1`, `s = 3`: the population moments of the marginal law
return the hyperparameters. -/
example : momShape (∑' k : ℕ, (k : ℝ) * marginalLik 2 1 3 k)
      (∑' k : ℕ, (k : ℝ) ^ 2 * marginalLik 2 1 3 k -
        (∑' k : ℕ, (k : ℝ) * marginalLik 2 1 3 k) ^ 2) = 2 :=
  (mom_marginal_moments (by norm_num) (by norm_num) (by norm_num)).1

/-- The second-moment hypothesis of `ae_tendsto_mom` is the marginal law's second moment, so the
hypothesis is satisfiable by the model's own pmf. -/
example {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    ∑' k : ℕ, (k : ℝ) ^ 2 * marginalLik a b s k =
      s * a / b + (s * a / b) ^ 2 / a + (s * a / b) ^ 2 := by
  simp only [funext (marginalLik_eq_negBinomialReal ha hb hs.le)]
  exact (hasSum_sq_negBinomialReal ha (by positivity)).tsum_eq

/-- The deterministic consistency core on exactly converging moments: constant sample moments
`M = 2`, `Q = 10` (variance `6`) give the constant estimate `â = 1`. -/
example : Tendsto (fun _ : ℕ => momShape 2 (10 - 2 ^ 2)) atTop (𝓝 (momShape 2 (10 - 2 ^ 2))) :=
  (tendsto_mom_of_tendsto (s := 1) one_pos two_pos (by norm_num) tendsto_const_nhds
    tendsto_const_nhds).1

end MathlibExtTest.Biology.Omics.HierarchicalCount
