/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OptimalStopping.SecretaryOptimality

/-!
# Tests for the optimality of the threshold rule in the secretary problem

The bound `card_rankRule_wins_div_factorial_le` is applied to constant rules, to the edge case
`n = 1`, and to the threshold rule `N_2` for `n = 3` written as a rule based on relative ranks,
which attains the bound `winProb 3 (optimalThreshold 3) = 1/2` (Ferguson, *Optimal Stopping and
Applications*, Chapter 2, §2.1).
-/

@[expose] public section

open MathlibExt.Probability.Secretary

namespace MathlibExtTest.Probability.OptimalStopping.SecretaryOptimality

/-- For `n = 3` the optimal threshold is `r₁ = 2`: `1 + 1/2 > 1 ≥ 1/2`. -/
theorem optimalThreshold_three : optimalThreshold 3 = 2 := by
  unfold optimalThreshold
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, fun m hm ⟨hm1, hT⟩ => ?_⟩
  · simp [harmonicTail]
    norm_num
  · have : m = 1 := by omega
    subst this
    simp [harmonicTail, Finset.sum_Ico_succ_top] at hT
    norm_num at hT

theorem winProb_three_optimalThreshold : winProb 3 (optimalThreshold 3) = 1 / 2 := by
  rw [optimalThreshold_three]
  simp [winProb, harmonicTail]
  norm_num

/-- `n = 1`: every rule selects the only applicant, and the bound applies with `r₁ = 1`. -/
example (s : Equiv.Perm (Fin 1) → Fin 1) :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin 1) => ∀ j, σ j ≤ σ (s σ)).card : ℝ) /
        (Nat.factorial 1) ≤ winProb 1 (optimalThreshold 1) :=
  card_rankRule_wins_div_factorial_le le_rfl s fun _ _ _ => Subsingleton.elim _ _

/-- `n = 1`: the bound is `winProb 1 1 = 1`, so it is attained. -/
example : winProb 1 (optimalThreshold 1) = 1 := by
  rw [le_antisymm (optimalThreshold_le le_rfl) (one_le_optimalThreshold 1)]
  simp [winProb, harmonicTail]

/-- A constant rule uses no information, so it is a rule based on relative ranks: always
selecting the first of four applicants wins with probability at most `winProb 4 r₁`. -/
example :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin 4) => ∀ j, σ j ≤ σ 0).card : ℝ) /
        (Nat.factorial 4) ≤ winProb 4 (optimalThreshold 4) :=
  card_rankRule_wins_div_factorial_le (s := fun _ => 0) (by norm_num) fun _ _ _ => rfl

/-- The threshold rule `N_2` for three applicants: select the applicant interviewed at time `1`
if better than the first one, and the last applicant otherwise. -/
def thresholdRuleThree (σ : Equiv.Perm (Fin 3)) : Fin 3 := if σ 0 < σ 1 then 1 else 2

/-- `thresholdRuleThree` only uses the relative order of the applicants seen so far. -/
theorem thresholdRuleThree_rank (σ σ' : Equiv.Perm (Fin 3))
    (h : ∀ j k : Fin 3, j ≤ thresholdRuleThree σ → k ≤ thresholdRuleThree σ →
      (σ j < σ k ↔ σ' j < σ' k)) :
    thresholdRuleThree σ' = thresholdRuleThree σ := by
  have h1 : (1 : Fin 3) ≤ thresholdRuleThree σ := by
    unfold thresholdRuleThree
    split_ifs <;> decide
  have h01 := h 0 1 ((Fin.zero_le _).trans h1) h1
  simp only [thresholdRuleThree, h01]

/-- `N_2` selects the best of three applicants for `3` of the `3! = 6` permutations. -/
theorem card_thresholdRuleThree_wins :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
      ∀ j, σ j ≤ σ (thresholdRuleThree σ)).card = 3 := by
  decide

/-- The bound is attained: `N_2` is a rule based on relative ranks with win probability
`1/2 = winProb 3 (optimalThreshold 3)`. -/
example :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
        ∀ j, σ j ≤ σ (thresholdRuleThree σ)).card : ℝ) / (Nat.factorial 3) =
      winProb 3 (optimalThreshold 3) := by
  rw [card_thresholdRuleThree_wins, winProb_three_optimalThreshold]
  norm_num [Nat.factorial]

example :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
        ∀ j, σ j ≤ σ (thresholdRuleThree σ)).card : ℝ) / (Nat.factorial 3) ≤
      winProb 3 (optimalThreshold 3) :=
  card_rankRule_wins_div_factorial_le (by norm_num) _ thresholdRuleThree_rank

/-- Always selecting the last of three applicants wins for `2` of the `6` permutations, below the
bound `1/2`. -/
example :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => ∀ j, σ j ≤ σ 2).card = 2 := by
  decide

end MathlibExtTest.Probability.OptimalStopping.SecretaryOptimality
