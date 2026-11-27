/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.StochasticShortestPath

/-! # Statewise Bellman residual bounds for greedy policies -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

open Matrix Simplex

variable {S A : Type*} [Fintype S] [DecidableEq S]
variable {M : MDP S A ℝ} {γ : ℝ}

/-- A deterministic policy of a stochastic MDP has a row-stochastic transition matrix. -/
lemma transitionMatrix_mem_rowStochastic (hM : M.Stochastic) (π : S → A) :
    transitionMatrix M π ∈ rowStochastic ℝ S := by
  rw [mem_rowStochastic_iff_sum]
  exact ⟨fun s y => hM.1 s (π s) y, fun s => hM.2 s (π s)⟩

/-- The difference between a policy's value and an estimate `W` is the value of a Markov
reward process with the same transition matrix and reward `Tπ W - W`. This expresses the
resolvent identity without introducing a second matrix-inverse API. -/
lemma policyValue_sub_eq_mrpValue_residual (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : S → A) (W : S → ℝ) :
    policyValue M γ hM hγ0 hγ1 π - W =
      mrpValue (transitionMatrix M π) (transitionMatrix_mem_rowStochastic hM π) hγ0 hγ1
        (policyBellman M γ π W - W) := by
  apply eq_mrpValue
  intro s
  have h := congrFun (policyBellman_policyValue hM hγ0 hγ1 π) s
  simp only [policyBellman, qValue] at h
  simp only [Pi.sub_apply, policyBellman, qValue, transitionMatrix, Matrix.of_apply,
    mul_sub, Finset.sum_sub_distrib]
  linarith only [h]

variable [Fintype A] [Nonempty A]

/-- The signed residual comparison. When `π` is greedy for `W` and `πstar` is optimal,
write `e = T W - W`. The loss `V* - Vπ` is at most the difference between the two
Markov reward process values for reward `e`, using their respective transitions. -/
lemma optimalValue_sub_policyValue_le_signed_residual
    (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W : S → ℝ) (π πstar : S → A)
    (hgreedy : policyBellman M γ π W = bellman M γ W)
    (hstar : policyValue M γ hM hγ0 hγ1 πstar = optimalValue M γ hM hγ0 hγ1) :
    let e := bellman M γ W - W
    optimalValue M γ hM hγ0 hγ1 - policyValue M γ hM hγ0 hγ1 π ≤
      mrpValue (transitionMatrix M πstar) (transitionMatrix_mem_rowStochastic hM πstar)
        hγ0 hγ1 e -
      mrpValue (transitionMatrix M π) (transitionMatrix_mem_rowStochastic hM π) hγ0 hγ1 e := by
  intro e
  have hπ := policyValue_sub_eq_mrpValue_residual hM hγ0 hγ1 π W
  rw [hgreedy] at hπ
  have hπstar := policyValue_sub_eq_mrpValue_residual hM hγ0 hγ1 πstar W
  rw [hstar] at hπstar
  have hle : policyBellman M γ πstar W - W ≤ e :=
    sub_le_sub_right (policyBellman_le_bellman πstar W) W
  have hmono := mrpValue_mono (transitionMatrix_mem_rowStochastic hM πstar) hγ0 hγ1 hle
  rw [← hπstar] at hmono
  intro s
  have h₁ := congrFun hπ s
  have h₂ := hmono s
  change optimalValue M γ hM hγ0 hγ1 s - W s ≤ _ at h₂
  change policyValue M γ hM hγ0 hγ1 π s - W s = _ at h₁
  change optimalValue M γ hM hγ0 hγ1 s - policyValue M γ hM hγ0 hγ1 π s ≤ _ - _
  linarith only [h₁, h₂]

/-- **Componentwise Bellman residual bound for a greedy policy.** For any policy `π` greedy for
`W` (ties allowed) and any optimal policy `πstar`, `V* - Vπ` lies between zero and the sum of
both policies' Markov reward process values with reward `|T W - W|`, pointwise.

Source: R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*,
SIAM J. Control Optim. 46(2), 2007, §4.2, Lemma 4.3, equation (4.6). -/
lemma optimalValue_sub_policyValue_le_abs_residual
    (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W : S → ℝ) (π πstar : S → A)
    (hgreedy : policyBellman M γ π W = bellman M γ W)
    (hstar : policyValue M γ hM hγ0 hγ1 πstar = optimalValue M γ hM hγ0 hγ1) :
    let e := fun s => |bellman M γ W s - W s|
    0 ≤ optimalValue M γ hM hγ0 hγ1 - policyValue M γ hM hγ0 hγ1 π ∧
    optimalValue M γ hM hγ0 hγ1 - policyValue M γ hM hγ0 hγ1 π ≤
      mrpValue (transitionMatrix M πstar) (transitionMatrix_mem_rowStochastic hM πstar)
        hγ0 hγ1 e +
      mrpValue (transitionMatrix M π) (transitionMatrix_mem_rowStochastic hM π) hγ0 hγ1 e := by
  intro e
  refine ⟨sub_nonneg.mpr (policyValue_le_optimalValue hM hγ0 hγ1 π), ?_⟩
  let r := bellman M γ W - W
  have hp : r ≤ e := fun s => le_abs_self (r s)
  have hn : -r ≤ e := fun s => neg_le_abs (r s)
  have h₁ := mrpValue_mono (transitionMatrix_mem_rowStochastic hM πstar) hγ0 hγ1 hp
  have h₂ := mrpValue_mono (transitionMatrix_mem_rowStochastic hM π) hγ0 hγ1 hn
  rw [mrpValue_neg] at h₂
  have h := optimalValue_sub_policyValue_le_signed_residual hM hγ0 hγ1 W π πstar hgreedy hstar
  exact h.trans (by rw [sub_eq_add_neg]; exact add_le_add h₁ h₂)

end Cslib.Algorithms.Lean.MarkovDecision
