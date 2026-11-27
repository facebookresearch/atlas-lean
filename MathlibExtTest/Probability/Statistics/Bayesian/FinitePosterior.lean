/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Bayesian.FiniteConsistency
public import MathlibExt.Probability.Statistics.Bayesian.FinitePosterior

@[expose] public section


namespace MathlibExtTest.Probability.Statistics.Bayesian.FinitePosterior

open MathlibExt.Probability.Statistics.Bayesian

/-- Hypotheses: `0` fair coin, `1` coin with heads probability `3/4`. -/
noncomputable def coinPrior : Fin 2 → ℝ := ![1/2, 1/2]
noncomputable def heads : Fin 2 → ℝ := ![1/2, 3/4]
noncomputable def tails : Fin 2 → ℝ := ![1/2, 1/4]
noncomputable def pointPrior : Fin 2 → ℝ := ![1, 0]
noncomputable def onlyBiased : Fin 2 → ℝ := ![0, 1]
noncomputable def zeroLik : Fin 2 → ℝ := ![0, 0]
noncomputable def heavyPrior : Fin 2 → ℝ := ![2, 2]

theorem coinPrior_nonneg : ∀ θ, 0 ≤ coinPrior θ := by
  intro θ; fin_cases θ <;> norm_num [coinPrior]

theorem coinPrior_sum : ∑ θ, coinPrior θ = 1 := by
  norm_num [coinPrior, Fin.sum_univ_two]

theorem coin_lik_nonneg : ∀ L ∈ [heads, heads, tails], ∀ θ, 0 ≤ L θ := by
  intro L hL θ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl <;> fin_cases θ <;> norm_num [heads, tails]

theorem coin_evidence_pos : 0 < finiteEvidence coinPrior (batchLikelihood [heads, heads, tails]) := by
  norm_num [finiteEvidence, batchLikelihood, coinPrior, heads, tails, Fin.sum_univ_two]

/-- Nonvacuity: the sequential posterior after heads, heads, tails is the batch posterior,
whose value at the biased coin is `9/17`. -/
theorem sequential_coin_value :
    sequentialPosterior coinPrior [heads, heads, tails] 1 = 9 / 17 := by
  rw [sequentialPosterior_eq_finitePosterior_batchLikelihood coinPrior_nonneg coinPrior_sum
    coin_lik_nonneg]
  norm_num [finitePosterior, finiteEvidence, batchLikelihood, coinPrior, heads, tails,
    Fin.sum_univ_two]

theorem sequential_coin_normalized :
    ∑ θ, sequentialPosterior coinPrior [heads, heads, tails] θ = 1 :=
  sum_sequentialPosterior coinPrior_nonneg coinPrior_sum coin_lik_nonneg coin_evidence_pos

/-- Order of the observations does not matter. -/
theorem sequential_coin_order :
    sequentialPosterior coinPrior [heads, heads, tails] =
      sequentialPosterior coinPrior [tails, heads, heads] :=
  sequentialPosterior_perm coinPrior_nonneg coinPrior_sum
    (List.perm_append_comm (l₁ := [heads, heads]) (l₂ := [tails])) coin_lik_nonneg

/-- Two-step update equals one update on the product likelihood. -/
theorem two_step_coin :
    finitePosterior (finitePosterior coinPrior heads) tails =
      finitePosterior coinPrior (fun θ => heads θ * tails θ) :=
  finitePosterior_finitePosterior (by norm_num [finiteEvidence, coinPrior, heads, Fin.sum_univ_two])

/-- Point-mass prior: the posterior stays the point mass. -/
theorem pointMass_posterior :
    finitePosterior pointPrior tails 0 = 1 ∧ finitePosterior pointPrior tails 1 = 0 := by
  have h1 : finitePosterior pointPrior tails 1 = 0 :=
    finitePosterior_eq_zero_of_mul_eq_zero (by norm_num [pointPrior])
  have hs := sum_finitePosterior (π := pointPrior) (L := tails)
    (by norm_num [finiteEvidence, pointPrior, tails, Fin.sum_univ_two])
  rw [Fin.sum_univ_two, h1] at hs
  exact ⟨by linarith, h1⟩

/-- Zero evidence: the totalized posterior is the zero function, so it is not normalized. -/
theorem zeroEvidence_not_normalized : ∑ θ, finitePosterior coinPrior zeroLik θ = 0 := by
  have hE : finiteEvidence coinPrior zeroLik = 0 := by
    norm_num [finiteEvidence, zeroLik, Fin.sum_univ_two]
  simp [finitePosterior_eq_zero_of_finiteEvidence_eq_zero hE]

/-- Prior-likelihood conflict: the point-mass prior on the fair coin meets an observation only
the biased coin can produce; the batch evidence is zero and the sequential result is zero. -/
theorem conflict_zero :
    finiteEvidence pointPrior (batchLikelihood [heads, onlyBiased]) = 0 ∧
      ∀ θ, sequentialPosterior pointPrior [heads, onlyBiased] θ = 0 := by
  have hE : finiteEvidence pointPrior (batchLikelihood [heads, onlyBiased]) = 0 := by
    norm_num [finiteEvidence, batchLikelihood, pointPrior, heads, onlyBiased, Fin.sum_univ_two]
  refine ⟨hE, fun θ => ?_⟩
  have h12 : finiteEvidence pointPrior (fun θ => heads θ * onlyBiased θ) = 0 := by
    norm_num [finiteEvidence, pointPrior, heads, onlyBiased, Fin.sum_univ_two]
  have hseq : finiteEvidence (finitePosterior pointPrior heads) onlyBiased = 0 := by
    rw [finiteEvidence_finitePosterior, h12, zero_div]
  simp only [sequentialPosterior]
  exact finitePosterior_eq_zero_of_finiteEvidence_eq_zero hseq θ

/-- Unnormalized prior: with no observations the sequential result is the prior itself (mass
4), so the batch identity needs `∑ π = 1`; one update already normalizes. -/
theorem heavyPrior_boundary :
    ∑ θ, sequentialPosterior heavyPrior [] θ = 4 ∧
      ∑ θ, finitePosterior heavyPrior heads θ = 1 := by
  refine ⟨by norm_num [sequentialPosterior, heavyPrior, Fin.sum_univ_two], ?_⟩
  exact sum_finitePosterior (by norm_num [finiteEvidence, heavyPrior, heads, Fin.sum_univ_two])

/-- Signed weights with zero first-step evidence: the two-step identity fails, so its
nonzero-evidence hypothesis cannot be dropped. -/
theorem two_step_needs_evidence :
    finitePosterior (finitePosterior ![1, 1] ![1, -1]) ![1, 0] (0 : Fin 2) ≠
      finitePosterior ![1, 1] (fun θ => (![1, -1] : Fin 2 → ℝ) θ * (![1, 0] : Fin 2 → ℝ) θ)
        (0 : Fin 2) := by
  norm_num [finitePosterior, finiteEvidence, Fin.sum_univ_two]

noncomputable def coinLik (θ x : Fin 2) : ℝ := if x = 0 then heads θ else tails θ

def flips (i : ℕ) (_ : Unit) : Fin 2 := if i = 2 then 1 else 0

/-- The existing finite-consistency weights are the sequential posterior. -/
theorem postWeight_coin_value : postWeight coinPrior coinLik flips 3 () 1 = 9 / 17 := by
  rw [postWeight_eq_sequentialPosterior coinPrior_nonneg coinPrior_sum
    (fun θ x => by unfold coinLik; split_ifs <;> fin_cases θ <;> norm_num [heads, tails])
    flips 3 ()]
  have hlist : ((List.range 3).map fun i θ => coinLik θ (flips i ())) = [heads, heads, tails] := by
    simp [List.range_succ, coinLik, flips]
  rw [hlist, sequential_coin_value]

/-- One more flip is one more Bayes update of the existing weights. -/
theorem postWeight_coin_step :
    postWeight coinPrior coinLik flips 3 () =
      finitePosterior (postWeight coinPrior coinLik flips 2 ()) tails := by
  rw [postWeight_succ coinPrior coinLik flips 2 ()
    (by norm_num [finiteEvidence, coinLik, flips, coinPrior, heads, tails, Fin.sum_univ_two,
      Finset.prod_range_succ])]
  have hstep : (fun θ => coinLik θ (flips 2 ())) = tails := by
    funext θ
    simp [coinLik, flips]
  rw [hstep]

end MathlibExtTest.Probability.Statistics.Bayesian.FinitePosterior

