/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.PolicyIteration
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Greedy policies of approximate values

Approximate dynamic programming acts greedily with respect to an estimate `V` of the optimal
value `V*`. Singh and Yee's bound (*An upper bound on the loss from approximate optimal-value
functions*, Machine Learning 16, 1994) controls the loss of the greedy policy by the estimation
error. Agarwal, Jiang, Kakade and Sun, *Reinforcement Learning: Theory and Algorithms*,
Lemma 1.11, is the action-value form, with constant `2 / (1 - γ)`; for a state-value estimate
acted on by one-step lookahead the constant is `2 γ / (1 - γ)`:

* `optimalValue_sub_policyValue_greedy_le`: if `|V s - V* s| ≤ d` for every state, the greedy
  policy `π = greedy M γ V` satisfies `0 ≤ V*(s) - V^π(s) ≤ 2 γ d / (1 - γ)` for every state.
* `optimalValue_sub_policyValue_greedy_valueIteration_le`: after `n` steps of value iteration
  from `V`, the greedy policy is within `2 γ / (1 - γ) * dist V (T V) * γ ^ n / (1 - γ)` of
  optimal in every state (compare AJKS Theorem 1.12, stated for Q-value iteration).
* `dist_optimalValue_policyValue_le_of_greedy`: any deterministic policy `π` with `T_π W = T W`,
  whatever its choice among tied maximizing actions, satisfies
  `‖V* - V^π‖∞ ≤ 2 γ / (1 - γ) * ‖V* - W‖∞` (Munos 2007, equation (2.3)).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] {M : MDP S A ℝ} {γ : ℝ}
  (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

include hM hγ0 hγ1

/-- **Singh and Yee's bound** (Singh and Yee 1994; cf. AJKS Lemma 1.11, the action-value form): if
`|V s - V* s| ≤ d` for every state `s`, then the policy selected by `greedy M γ V` loses at most
`2 γ d / (1 - γ)` against the optimal value in every state. -/
theorem optimalValue_sub_policyValue_greedy_le {V : S → ℝ} {d : ℝ}
    (hV : ∀ s, |V s - optimalValue M γ hM hγ0 hγ1 s| ≤ d) (s : S) :
    0 ≤ optimalValue M γ hM hγ0 hγ1 s - policyValue M γ hM hγ0 hγ1 (greedy M γ V) s ∧
      optimalValue M γ hM hγ0 hγ1 s - policyValue M γ hM hγ0 hγ1 (greedy M γ V) s ≤
        2 * γ * d / (1 - γ) := by
  set Vs := optimalValue M γ hM hγ0 hγ1
  set π := greedy M γ V
  have h1γ : 0 < 1 - γ := by linarith
  refine ⟨sub_nonneg.2 (policyValue_le_optimalValue hM hγ0 hγ1 π s), ?_⟩
  set c := 2 * γ * d / (1 - γ)
  -- `V* - c` lies below its Bellman image under `π`, hence below `V^π`
  have key : (fun s => Vs s - c) ≤ policyBellman M γ π (fun s => Vs s - c) := by
    intro s
    have hshift : policyBellman M γ π (fun s => Vs s - c) s = policyBellman M γ π Vs s - γ * c := by
      simp only [policyBellman, qValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hM.2 s (π s), one_mul]
      ring
    have h1 : |policyBellman M γ π V s - policyBellman M γ π Vs s| ≤ γ * d :=
      abs_policyBellman_sub_le hM hγ0 π hV s
    have h2 : |bellman M γ V s - bellman M γ Vs s| ≤ γ * d := abs_bellman_sub_le hM hγ0 hV s
    have h3 : policyBellman M γ π V s = bellman M γ V s := by
      rw [show π = greedy M γ V from rfl, policyBellman_greedy]
    have h4 : bellman M γ Vs s = Vs s := congrFun (bellman_optimalValue hM hγ0 hγ1) s
    rw [abs_le] at h1 h2
    have hc : c - γ * c = 2 * γ * d := by
      simp only [c]
      field_simp
    rw [hshift]
    linarith [h1.1, h2.1]
  have := le_policyValue_of_le_policyBellman hM hγ0 hγ1 π key s
  linarith

/-- **Greedy policies of value iteration** (compare AJKS Theorem 1.12): after `n` steps of value
iteration from `V`, the policy selected by `greedy M γ (valueIteration M γ n V)` loses at most
`2 γ / (1 - γ) * (dist V (T V) * γ ^ n / (1 - γ))` against the optimal value in every state. -/
theorem optimalValue_sub_policyValue_greedy_valueIteration_le (V : S → ℝ) (n : ℕ) (s : S) :
    optimalValue M γ hM hγ0 hγ1 s -
        policyValue M γ hM hγ0 hγ1 (greedy M γ (valueIteration M γ n V)) s ≤
      2 * γ * (dist V (bellman M γ V) * γ ^ n / (1 - γ)) / (1 - γ) := by
  have hd := dist_valueIteration_le hM hγ0 hγ1 V n
  refine (optimalValue_sub_policyValue_greedy_le hM hγ0 hγ1 (fun s' => ?_) s).2
  rw [← Real.dist_eq]
  exact (dist_le_pi_dist _ _ s').trans hd

/-- **Sup-norm loss for any greedy policy** (Munos 2007, equation (2.3)). For a stochastic MDP
with finite nonempty state and action sets, real rewards and `0 ≤ γ < 1`, let `W` be a value
estimate and `π` a deterministic stationary policy such that `T_π W = T W`. Then the sup-norm
loss `‖V* - V^π‖∞` is at most `2 γ / (1 - γ) * ‖V* - W‖∞`. The equality permits any choice
among tied maximizing actions. -/
lemma dist_optimalValue_policyValue_le_of_greedy [Nonempty S] (W : S → ℝ) (π : S → A)
    (hgreedy : policyBellman M γ π W = bellman M γ W) :
    dist (optimalValue M γ hM hγ0 hγ1) (policyValue M γ hM hγ0 hγ1 π) ≤
      2 * γ / (1 - γ) * dist (optimalValue M γ hM hγ0 hγ1) W := by
  let Vstar := optimalValue M γ hM hγ0 hγ1
  let Vπ := policyValue M γ hM hγ0 hγ1 π
  have hT := (bellman_contracting hM hγ0 hγ1).dist_le_mul Vstar W
  have hπ := (policyBellman_contracting hM hγ0 hγ1 π).dist_le_mul W Vπ
  rw [Real.coe_toNNReal γ hγ0] at hT hπ
  have hW : dist W Vπ ≤ dist Vstar W + dist Vstar Vπ := by
    simpa only [dist_comm W Vstar] using dist_triangle W Vstar Vπ
  have h : dist Vstar Vπ ≤ γ * dist Vstar W + γ * (dist Vstar W + dist Vstar Vπ) := calc
    dist Vstar Vπ = dist (bellman M γ Vstar) (policyBellman M γ π Vπ) := by
      rw [show bellman M γ Vstar = Vstar from bellman_optimalValue hM hγ0 hγ1,
        show policyBellman M γ π Vπ = Vπ from policyBellman_policyValue hM hγ0 hγ1 π]
    _ ≤ dist (bellman M γ Vstar) (bellman M γ W) +
        dist (policyBellman M γ π W) (policyBellman M γ π Vπ) := by
      rw [hgreedy]
      exact dist_triangle _ _ _
    _ ≤ γ * dist Vstar W + γ * dist W Vπ := add_le_add hT hπ
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hW hγ0)
  change dist Vstar Vπ ≤ 2 * γ / (1 - γ) * dist Vstar W
  rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.mpr hγ1)]
  linarith only [h]

end Cslib.Algorithms.Lean.MarkovDecision
