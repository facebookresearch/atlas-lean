/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CoxPartialLikelihood

@[expose] public section

open Finset Real
open MathlibExt.Probability.Statistics.CoxPartialLikelihood

namespace MathlibExtTest.Probability.Statistics.CoxPartialLikelihood

/-- Two subjects, both with observed events, at times `1` and `2`. -/
noncomputable def T₀ : Fin 2 → ℝ := ![1, 2]

/-- Both events are observed. -/
def δ₀ : Fin 2 → Bool := ![true, true]

/-- Subject `0` is in group 1, subject `1` in group 0. -/
def g₀ : Fin 2 → Bool := ![true, false]

theorem riskSet_T₀_zero : riskSet T₀ 0 = univ := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, iff_true]
  fin_cases l <;> norm_num [T₀]

theorem riskSet_T₀_one : riskSet T₀ 1 = {1} := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, mem_singleton]
  fin_cases l <;> norm_num [T₀]

theorem filter_δ₀ : univ.filter (fun i => δ₀ i = true) = univ := by decide

theorem filter_g₀_univ : univ.filter (fun l => g₀ l = true) = {0} := by decide

theorem filter_g₀_one : ({1} : Finset (Fin 2)).filter (fun l => g₀ l = true) = ∅ := by
  decide

/-- `O - E = (1 - 1/2) + (0 - 0/1) = 1/2`, and it is the Cox score at `β = 0`. -/
example : coxScore T₀ δ₀ (groupIndicator g₀) 0 = 1 / 2 := by
  rw [coxScore_zero, observedMinusExpected, filter_δ₀, Fin.sum_univ_two]
  simp only [numAtRisk, numAtRiskIn, riskSet_T₀_zero, riskSet_T₀_one, filter_g₀_univ,
    filter_g₀_one]
  norm_num [groupIndicator, g₀]

/-- The Breslow information `1·1/2² + 0·1/1² = 1/4` is the Cox information at `β = 0`
(event times here are distinct, so it also equals the log-rank variance). -/
example : coxInformation T₀ δ₀ (groupIndicator g₀) 0 = 1 / 4 := by
  rw [coxInformation_zero, breslowInformation, filter_δ₀, Fin.sum_univ_two]
  simp only [numAtRisk, numAtRiskIn, riskSet_T₀_zero, riskSet_T₀_one, filter_g₀_univ,
    filter_g₀_one]
  norm_num

/-- Concavity, the score and the information for this sample. -/
example : ConcaveOn ℝ Set.univ
    (logPartialLikelihood T₀ δ₀ (fun i (_ : Fin 1) => groupIndicator g₀ i)) :=
  concaveOn_logPartialLikelihood _ _ _

example (b : ℝ) :
    HasDerivAt (logPartialLikelihood₁ T₀ δ₀ (groupIndicator g₀))
      (coxScore T₀ δ₀ (groupIndicator g₀) b) b :=
  hasDerivAt_logPartialLikelihood _ _ _ b

/-- A censored subject contributes no factor: with no events the partial likelihood is `1`. -/
example (x : Fin 2 → Fin 1 → ℝ) (β : Fin 1 → ℝ) :
    partialLikelihood T₀ (fun _ => false) x β = 1 := by
  simp [partialLikelihood]

#print axioms concaveOn_logPartialLikelihood
#print axioms coxScore_zero
#print axioms hasDerivAt_coxScore

/-! ### The vector score -/

/-- Three subjects at times `1, 2, 3`; subject `1` is censored. -/
noncomputable def T₁ : Fin 3 → ℝ := ![1, 2, 3]

/-- Subjects `0` and `2` have observed events. -/
def δ₁ : Fin 3 → Bool := ![true, false, true]

/-- Two covariates: `x₀ = (1, 0)`, `x₁ = (0, 1)`, `x₂ = (1, 1)`. -/
def x₁ : Fin 3 → Fin 2 → ℝ := ![![1, 0], ![0, 1], ![1, 1]]

theorem riskSet_T₁_zero : riskSet T₁ 0 = univ := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, iff_true]
  fin_cases l <;> norm_num [T₁]

theorem riskSet_T₁_two : riskSet T₁ 2 = {2} := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, mem_singleton]
  fin_cases l <;> norm_num [T₁]

theorem filter_δ₁ : univ.filter (fun i => δ₁ i = true) = {0, 2} := by decide

/-- At `β = 0` the weighted mean over the full risk set is the plain mean `(2/3, 2/3)`. -/
example : riskMeanVec T₁ x₁ 0 0 = ![2 / 3, 2 / 3] := by
  funext j
  rw [riskMeanVec_apply, riskSet_T₁_zero]
  fin_cases j <;> simp [x₁, Fin.sum_univ_three] <;> norm_num

/-- At `β = 0` the score vector is observed minus expected covariates,
`(x₀ - (2/3, 2/3)) + (x₂ - x₂) = (1/3, -2/3)`. -/
example : coxGradient T₁ δ₁ x₁ 0 = ![1 / 3, -2 / 3] := by
  funext j
  simp only [coxGradient, filter_δ₁, Finset.sum_apply, Pi.sub_apply, riskMeanVec_apply]
  rw [sum_pair (by decide), riskSet_T₁_zero, riskSet_T₁_two]
  fin_cases j <;> simp [x₁, Fin.sum_univ_three] <;> norm_num

/-- For one covariate the score vector is the scalar score; here `coxScore` is evaluated from its
defining sums: `(1 - 1/2) + (0 - 0) = 1/2`. -/
example : coxGradient T₀ δ₀ (fun i (_ : Fin 1) => groupIndicator g₀ i) (fun _ => 0) =
    fun _ => 1 / 2 := by
  rw [coxGradient_one]
  funext _
  rw [coxScore, filter_δ₀, Fin.sum_univ_two]
  simp only [riskMean, riskSet_T₀_zero, riskSet_T₀_one, zero_mul, exp_zero, mul_one,
    Fin.sum_univ_two, sum_singleton]
  norm_num [groupIndicator, g₀]

/-- The derivative and gradient theorems on the three-subject sample. -/
example (β : Fin 2 → ℝ) :
    HasFDerivAt (logPartialLikelihood T₁ δ₁ x₁)
      (∑ j, coxGradient T₁ δ₁ x₁ β j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) j) β :=
  hasFDerivAt_logPartialLikelihood _ _ _ β

example (β : Fin 2 → ℝ) :
    HasGradientAt (fun b : EuclideanSpace ℝ (Fin 2) => logPartialLikelihood T₁ δ₁ x₁ b.ofLp)
      (WithLp.toLp 2 (coxGradient T₁ δ₁ x₁ β)) (WithLp.toLp 2 β) :=
  hasGradientAt_logPartialLikelihood _ _ _ β

/-- The Hessian quadratic form at `β = 0` along `u = (1, 0)`: the risk set of subject `0` has
first-covariate values `1, 0, 1` (variance `2/3 - 4/9 = 2/9`), subject `2` alone has variance
`0`, so `d/dt ⟪U(t u), u⟫ = -2/9`. -/
example : HasDerivAt (fun t : ℝ => coxGradient T₁ δ₁ x₁ (0 + t • ![1, 0]) ⬝ᵥ ![1, 0])
    (-(2 / 9)) 0 := by
  convert hasDerivAt_coxGradient_dotProduct T₁ δ₁ x₁ 0 ![1, 0] using 2
  rw [filter_δ₁, sum_pair (by decide)]
  simp only [riskVarAlong, riskMeanVec_apply, dotProduct, riskSet_T₁_zero, riskSet_T₁_two]
  simp [x₁, Fin.sum_univ_three]
  norm_num

/-- The directional variance at `p = 1` is the scalar `riskVar`. -/
example (b : ℝ) (i : Fin 2) :
    riskVarAlong T₀ (fun i (_ : Fin 1) => groupIndicator g₀ i) (fun _ => b) (fun _ => 1) i =
      riskVar T₀ (groupIndicator g₀) b i :=
  riskVarAlong_one _ _ _ _

#print axioms hasFDerivAt_logPartialLikelihood
#print axioms hasGradientAt_logPartialLikelihood
#print axioms coxGradient_one
#print axioms hasDerivAt_coxGradient_dotProduct
#print axioms riskVarAlong_one

end MathlibExtTest.Probability.Statistics.CoxPartialLikelihood
