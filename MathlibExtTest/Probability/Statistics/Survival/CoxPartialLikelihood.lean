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

end MathlibExtTest.Probability.Statistics.CoxPartialLikelihood
