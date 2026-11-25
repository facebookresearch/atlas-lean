/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OptimalStopping.Secretary
public import MathlibExt.Probability.OptimalStopping.SecretaryModel

/-!
# Tests for the secretary problem

Values from Ferguson's table (*Optimal Stopping and Applications*, Chapter 2, §2.1):
`P_2 = 1/2` for `n = 3`, `P_2 = 11/24 ≈ .458` for `n = 4`, and the optimal threshold for
`n = 4` is `r₁ = 2`.
-/

@[expose] public section

open MathlibExt.Probability.Secretary

namespace MathlibExtTest.Probability.OptimalStopping.Secretary

/-- `n = 3`, `r = 2`: `P_2 = (1 + 1/2)/3 = 1/2`. -/
example : winProb 3 2 = 1 / 2 := by
  simp [winProb, harmonicTail]
  norm_num

/-- `n = 4`, `r = 2`: `P_2 = (1 + 1/2 + 1/3)/4 = 11/24`. -/
example : winProb 4 2 = 11 / 24 := by
  simp [winProb, harmonicTail, Finset.sum_Ico_succ_top]
  norm_num

/-- `n = 1`: the only threshold is `r = 1` and the win probability is `1`. -/
example : winProb 1 1 = 1 := by
  simp [winProb, harmonicTail]

/-- For `n = 4` the optimal threshold is `r₁ = 2`: `1 + 1/2 + 1/3 > 1 ≥ 1/2 + 1/3`. -/
example : optimalThreshold 4 = 2 := by
  unfold optimalThreshold
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, fun m hm ⟨hm1, hT⟩ => ?_⟩
  · simp [harmonicTail, Finset.sum_Ico_succ_top]
    norm_num
  · have : m = 1 := by omega
    subst this
    simp [harmonicTail, Finset.sum_Ico_succ_top] at hT
    norm_num at hT

/-- The random-order model with `n = 3` applicants and threshold `r = 2`: the rule wins for half
of the `3! = 6` permutations. -/
example :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
        ∃ i : Fin 3, 2 - 1 ≤ (i : ℕ) ∧ (∀ j, j < i → σ j < σ i) ∧
          (∀ k : Fin 3, 2 - 1 ≤ (k : ℕ) → k < i → ∃ j, j < k ∧ σ k < σ j) ∧
          ∀ j, σ j ≤ σ i).card : ℝ) / (Nat.factorial 3) = 1 / 2 := by
  rw [card_thresholdRule_wins_div_factorial (by norm_num) (by norm_num)]
  simp [winProb, harmonicTail]
  norm_num

end MathlibExtTest.Probability.OptimalStopping.Secretary
