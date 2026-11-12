/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.CountData.Model

@[expose] public section

open Finset Real Matrix ProbabilityTheory
open MathlibExt.Probability.Statistics.GLM.NegativeBinomial
open MathlibExt.Probability.Statistics.GLM.CountData

namespace MathlibExtTest.Probability.Statistics.GLM.CountData.Model

/-! ### The selected law -/

/-- Poisson at mean `1`: `P(0) = e^{-1}`. -/
example : CountLaw.poisson.pmf 1 0 = exp (-1) := CountLaw.pmf_poisson_zero zero_le_one

/-- Negative binomial with shape `1` (geometric) at mean `1`: `P(0) = 1 / 2`. -/
example : (CountLaw.negBinomial 1).pmf 1 0 = 1 / 2 := by
  rw [CountLaw.pmf_negBinomial_zero]
  norm_num

/-- The negative binomial puts strictly more mass at zero than the Poisson law with the same
mean: `1 / 2 > e^{-1}`. -/
example : CountLaw.poisson.pmf 1 0 < (CountLaw.negBinomial 1).pmf 1 0 := by
  rw [CountLaw.pmf_poisson_zero zero_le_one, CountLaw.pmf_negBinomial_zero, Real.exp_neg,
    Real.rpow_one, inv_lt_comm₀ (exp_pos 1) (by norm_num)]
  have h := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
  norm_num at h ⊢
  linarith

/-- Variance functions: Poisson `V(2) = 2`; negative binomial with shape `2`,
`V(2) = 2 + 4 / 2 = 4`. -/
example : CountLaw.poisson.varianceFn 2 = 2 := by norm_num [CountLaw.varianceFn]

example : (CountLaw.negBinomial 2).varianceFn 2 = 4 := by norm_num [CountLaw.varianceFn]

/-- The mean–variance law, instantiated for the negative binomial with shape `2` at mean `2`. -/
example :
    ∑' k : ℕ, (k : ℝ) ^ 2 * (CountLaw.negBinomial 2).pmf 2 k -
        (∑' k : ℕ, (k : ℝ) * (CountLaw.negBinomial 2).pmf 2 k) ^ 2 = 4 := by
  rw [CountLaw.variance_pmf (show (CountLaw.negBinomial 2).Valid from two_pos) zero_le_two]
  norm_num [CountLaw.varianceFn]

/-- The dispersion parametrization: dispersion `1 / 2` is the negative binomial with shape `2`. -/
example : CountLaw.ofDispersion (1 / 2) = CountLaw.negBinomial 2 := by
  rw [CountLaw.ofDispersion_of_ne_zero (by norm_num)]
  norm_num

example : (CountLaw.ofDispersion 0).Valid := CountLaw.valid_ofDispersion le_rfl

/-- At mean `0` (boundary) the Poisson law is the point mass at `0`. -/
example : CountLaw.poisson.pmf 0 3 = 0 := by
  rw [CountLaw.pmf_mean_zero (show CountLaw.poisson.Valid from trivial)]
  norm_num

/-! ### A two-sample model -/

/-- One gene, two samples of conditions `0` and `1`; sample `1` has library size `0`. -/
noncomputable def toy (L : CountLaw) : CountModel Unit (Fin 2) (Fin 2) where
  law := fun _ => L
  condition := id
  librarySize := ![2, 0]
  rate := fun _ c => if c = 0 then 3 else 5

theorem toy_valid {L : CountLaw} (hL : L.Valid) : (toy L).Valid where
  law_valid := fun _ => hL
  librarySize_nonneg := fun j => by fin_cases j <;> simp [toy]
  rate_pos := fun _ c => by simp only [toy]; split_ifs <;> norm_num

/-- The mean of sample `0` is `2 · 3 = 6`. -/
example (L : CountLaw) : (toy L).mean () 0 = 6 := by norm_num [toy, CountModel.mean]

/-- Sample `1` has library size `0`, so a count of `4` there has probability `0`, whatever the
rate `5` of its condition. -/
example {L : CountLaw} (hL : L.Valid) : (toy L).countPMF () 1 4 = 0 := by
  rw [CountModel.countPMF_of_librarySize_eq_zero (toy_valid hL) () (by simp [toy])]
  norm_num

/-- Hence a count matrix with a nonzero count in sample `1` has likelihood `0`. -/
example {L : CountLaw} (hL : L.Valid) : (toy L).likelihood (fun _ => ![7, 4]) = 0 :=
  CountModel.likelihood_eq_zero (g := ()) (j := 1) (toy_valid hL) (by simp [toy]) (by simp)

/-- In sample `0` (library size `2 > 0`) a zero count is possible but not certain. -/
example {L : CountLaw} (hL : L.Valid) :
    0 < (toy L).countPMF () 0 0 ∧ (toy L).countPMF () 0 0 < 1 := by
  have hs : 0 < (toy L).librarySize 0 := by norm_num [toy]
  exact ⟨CountLaw.pmf_pos hL (CountModel.mean_pos (toy_valid hL) () hs) 0,
    ((CountModel.countPMF_zero_mem (toy_valid hL) () hs)).2⟩

/-- Normalization recovers the rate of sample `0`'s condition. -/
example (L : CountLaw) : (toy L).mean () 0 / (toy L).librarySize 0 = 3 := by
  rw [CountModel.mean_div_librarySize () (by norm_num [toy])]
  simp [toy]

/-- The condition design of the identity condition map is the identity matrix pattern. -/
example : CountModel.conditionDesign (id : Fin 2 → Fin 2) 0 1 = 0 := by
  simp [CountModel.conditionDesign]

example (β : Fin 2 → ℝ) : (CountModel.conditionDesign (id : Fin 2 → Fin 2) *ᵥ β) 1 = β 1 :=
  CountModel.conditionDesign_mulVec id β 1

/-! ### The regression bridge on a one-sample model -/

/-- One gene, one sample with library size `1` and rate `1`, negative binomial with shape `1`. -/
noncomputable def single : CountModel Unit Unit Unit where
  law := fun _ => CountLaw.negBinomial 1
  condition := id
  librarySize := fun _ => 1
  rate := fun _ _ => 1

theorem single_valid : single.Valid where
  law_valid := fun _ => one_pos
  librarySize_nonneg := fun _ => zero_le_one
  rate_pos := fun _ _ => one_pos

/-- The bridge for the one-sample model: the log-likelihood of any count is the rate-free
constant plus `nbLogLik` with offset `log 1` and coefficient `log 1`. -/
example (Y : Unit → Unit → ℕ) :
    ∑ j, log (single.countPMF () j (Y () j)) =
      ∑ j, (log ((ascPochhammer ℝ (Y () j)).eval 1 / (Y () j).factorial) + 1 * log 1) +
        nbLogLik 1 (CountModel.conditionDesign single.condition)
          (fun j => log (single.librarySize j)) (fun j => (Y () j : ℝ))
          (fun c => log (single.rate () c)) :=
  CountModel.sum_log_countPMF_eq_nbLogLik single_valid rfl (fun _ => one_pos) Y

/-- Non-vacuity of the bridge: the left side at the count `0` is `log (1 / 2)`, the log
probability of a zero count under the geometric law with mean `1`. -/
example : log (single.countPMF () () 0) = log (1 / 2) := by
  rw [CountModel.countPMF, show single.mean () () = 1 by norm_num [single, CountModel.mean]]
  rw [show single.law () = CountLaw.negBinomial 1 from rfl, CountLaw.pmf_negBinomial_zero]
  norm_num

end MathlibExtTest.Probability.Statistics.GLM.CountData.Model
