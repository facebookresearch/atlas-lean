/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.FiniteHorizonTerminal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Finite-horizon terminal-value tests (contract C5)

Concrete two-state two-action checks for
`CSLibExt/Algorithms/Lean/MDP/FiniteHorizonTerminal.lean` with nonzero terminal
values. A deterministic salvage model shows the terminal value changes the
optimal first action; horizon-0, `γ = 0`, `γ = 1`, `g = 0` agreement, a
negated-cost minimization instance, failure of naive unshaped addition, and a
`γ < 0` counterexample to domination are all pinned. Both independently reduced
values and applications of the exported theorems are included.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

namespace FiniteHorizon

private def salvageReward (s a : Fin 2) : ℝ :=
  if s = 0 ∧ a = 0 then 1 else 0

private def salvageProb (s a s' : Fin 2) : ℝ :=
  if s = 0 then
    if a = 0 then (if s' = 0 then 1 else 0)
    else (if s' = 1 then 1 else 0)
  else (if s' = 1 then 1 else 0)

private def salvageMDP : MDP (Fin 2) (Fin 2) ℝ where
  reward := salvageReward
  prob := salvageProb

private def salvageG : Fin 2 → ℝ := fun s => if s = 0 then 0 else 4

private theorem salvageReward_00 : salvageReward 0 0 = 1 := by
  unfold salvageReward
  simp

private theorem salvageReward_01 : salvageReward 0 1 = 0 := by
  unfold salvageReward
  simp

private theorem salvageReward_10 : salvageReward 1 0 = 0 := by
  unfold salvageReward
  simp

private theorem salvageG_0 : salvageG 0 = 0 := by
  unfold salvageG
  simp

private theorem salvageG_1 : salvageG 1 = 4 := by
  unfold salvageG
  simp

private theorem salvageProb_000 : salvageProb 0 0 0 = 1 := by
  unfold salvageProb
  simp

private theorem salvageProb_001 : salvageProb 0 0 1 = 0 := by
  unfold salvageProb
  simp

private theorem salvageProb_010 : salvageProb 0 1 0 = 0 := by
  unfold salvageProb
  simp

private theorem salvageProb_011 : salvageProb 0 1 1 = 1 := by
  unfold salvageProb
  simp

private theorem salvageProb_101 : salvageProb 1 0 1 = 1 := by
  unfold salvageProb
  simp

private theorem salvageProb_100 : salvageProb 1 0 0 = 0 := by
  unfold salvageProb
  simp

private theorem salvageProb_110 : salvageProb 1 1 0 = 0 := by
  unfold salvageProb
  simp

private theorem salvageProb_111 : salvageProb 1 1 1 = 1 := by
  unfold salvageProb
  simp

private theorem salvageReward_11 : salvageReward 1 1 = 0 := by
  unfold salvageReward
  simp

private theorem salvageMDP_stochastic : salvageMDP.Stochastic := by
  constructor
  · intro s a s'
    fin_cases s <;> fin_cases a <;> fin_cases s' <;> simp [salvageMDP, salvageProb]
  · intro s a
    fin_cases s <;> fin_cases a
    · rw [Fin.sum_univ_two]
      show salvageMDP.prob 0 0 0 + salvageMDP.prob 0 0 1 = 1
      have h0 : salvageMDP.prob 0 0 0 = 1 := salvageProb_000
      have h1 : salvageMDP.prob 0 0 1 = 0 := salvageProb_001
      rw [h0, h1]
      ring
    · rw [Fin.sum_univ_two]
      show salvageMDP.prob 0 1 0 + salvageMDP.prob 0 1 1 = 1
      have h0 : salvageMDP.prob 0 1 0 = 0 := salvageProb_010
      have h1 : salvageMDP.prob 0 1 1 = 1 := salvageProb_011
      rw [h0, h1]
      ring
    · rw [Fin.sum_univ_two]
      show salvageMDP.prob 1 0 0 + salvageMDP.prob 1 0 1 = 1
      have h0 : salvageMDP.prob 1 0 0 = 0 := salvageProb_100
      have h1 : salvageMDP.prob 1 0 1 = 1 := salvageProb_101
      rw [h0, h1]
      ring
    · rw [Fin.sum_univ_two]
      show salvageMDP.prob 1 1 0 + salvageMDP.prob 1 1 1 = 1
      have h0 : salvageMDP.prob 1 1 0 = 0 := salvageProb_110
      have h1 : salvageMDP.prob 1 1 1 = 1 := salvageProb_111
      rw [h0, h1]
      ring

private theorem fin2_sup'_eq {f : Fin 2 → ℝ} {m : ℝ} (h0 : f 0 ≤ m) (h1 : f 1 ≤ m)
    (a : Fin 2) (ha : f a = m) : Finset.univ.sup' Finset.univ_nonempty f = m := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro b _
    fin_cases b
    · exact h0
    · exact h1
  · rw [← ha]
    exact Finset.le_sup' f (Finset.mem_univ a)

private theorem salvage_q_half_g_00 : qValue salvageMDP (1 / 2) salvageG 0 0 = 1 := by
  unfold qValue
  show salvageReward 0 0 + (1 / 2) * ∑ s', salvageProb 0 0 s' * salvageG s' = 1
  rw [Fin.sum_univ_two, salvageProb_000, salvageProb_001, salvageG_0, salvageG_1,
    salvageReward_00]
  ring

private theorem salvage_q_half_g_01 : qValue salvageMDP (1 / 2) salvageG 0 1 = 2 := by
  unfold qValue
  show salvageReward 0 1 + (1 / 2) * ∑ s', salvageProb 0 1 s' * salvageG s' = 2
  rw [Fin.sum_univ_two, salvageProb_010, salvageProb_011, salvageG_0, salvageG_1,
    salvageReward_01]
  ring

private theorem salvage_q_half_g_10 : qValue salvageMDP (1 / 2) salvageG 1 0 = 2 := by
  unfold qValue
  show salvageReward 1 0 + (1 / 2) * ∑ s', salvageProb 1 0 s' * salvageG s' = 2
  rw [Fin.sum_univ_two, salvageProb_100, salvageProb_101, salvageG_0, salvageG_1,
    salvageReward_10]
  ring

private theorem salvage_q_half_g_11 : qValue salvageMDP (1 / 2) salvageG 1 1 = 2 := by
  unfold qValue
  show salvageReward 1 1 + (1 / 2) * ∑ s', salvageProb 1 1 s' * salvageG s' = 2
  rw [Fin.sum_univ_two, salvageProb_110, salvageProb_111, salvageG_0, salvageG_1,
    salvageReward_11]
  ring

private theorem salvage_VI_half_1_0 : valueIteration salvageMDP (1 / 2) 1 salvageG 0 = 2 := by
  show bellman salvageMDP (1 / 2) salvageG 0 = 2
  unfold bellman
  exact fin2_sup'_eq (by rw [salvage_q_half_g_00]; norm_num)
    (by rw [salvage_q_half_g_01]) 1 salvage_q_half_g_01

private theorem salvage_VI_half_1_1 : valueIteration salvageMDP (1 / 2) 1 salvageG 1 = 2 := by
  show bellman salvageMDP (1 / 2) salvageG 1 = 2
  unfold bellman
  exact fin2_sup'_eq (by rw [salvage_q_half_g_10])
    (by rw [salvage_q_half_g_11]) 0 salvage_q_half_g_10

private theorem salvage_q_half_zero_00 : qValue salvageMDP (1 / 2) (fun _ => 0) 0 0 = 1 := by
  unfold qValue
  show salvageReward 0 0 + (1 / 2) * ∑ s', salvageProb 0 0 s' * (0 : ℝ) = 1
  rw [salvageReward_00]
  simp

private theorem salvage_q_half_zero_01 : qValue salvageMDP (1 / 2) (fun _ => 0) 0 1 = 0 := by
  unfold qValue
  show salvageReward 0 1 + (1 / 2) * ∑ s', salvageProb 0 1 s' * (0 : ℝ) = 0
  rw [salvageReward_01]
  simp

private theorem salvage_q_half_zero_10 : qValue salvageMDP (1 / 2) (fun _ => 0) 1 0 = 0 := by
  unfold qValue
  show salvageReward 1 0 + (1 / 2) * ∑ s', salvageProb 1 0 s' * (0 : ℝ) = 0
  rw [salvageReward_10]
  simp

private theorem salvage_q_half_zero_11 : qValue salvageMDP (1 / 2) (fun _ => 0) 1 1 = 0 := by
  unfold qValue
  show salvageReward 1 1 + (1 / 2) * ∑ s', salvageProb 1 1 s' * (0 : ℝ) = 0
  rw [salvageReward_11]
  simp

private theorem salvage_FHV_half_1_0 : finiteHorizonValue salvageMDP (1 / 2) 1 0 = 1 := by
  rw [finiteHorizonValue_succ]
  show bellman salvageMDP (1 / 2) (finiteHorizonValue salvageMDP (1 / 2) 0) 0 = 1
  rw [finiteHorizonValue_zero]
  show bellman salvageMDP (1 / 2) (fun _ => 0) 0 = 1
  unfold bellman
  exact fin2_sup'_eq (by rw [salvage_q_half_zero_00])
    (by rw [salvage_q_half_zero_01]; norm_num) 0 salvage_q_half_zero_00

private theorem salvage_FHV_half_1_1 : finiteHorizonValue salvageMDP (1 / 2) 1 1 = 0 := by
  rw [finiteHorizonValue_succ]
  show bellman salvageMDP (1 / 2) (finiteHorizonValue salvageMDP (1 / 2) 0) 1 = 0
  rw [finiteHorizonValue_zero]
  show bellman salvageMDP (1 / 2) (fun _ => 0) 1 = 0
  unfold bellman
  exact fin2_sup'_eq (by rw [salvage_q_half_zero_10])
    (by rw [salvage_q_half_zero_11]) 0 salvage_q_half_zero_10

private theorem salvage_best_with_terminal :
    qValue salvageMDP (1 / 2) salvageG 0 0 < qValue salvageMDP (1 / 2) salvageG 0 1 := by
  rw [salvage_q_half_g_00, salvage_q_half_g_01]
  norm_num

private theorem salvage_best_without_terminal :
    qValue salvageMDP (1 / 2) (fun _ => 0) 0 1 < qValue salvageMDP (1 / 2) (fun _ => 0) 0 0 := by
  rw [salvage_q_half_zero_01, salvage_q_half_zero_00]
  norm_num

private theorem salvage_VI_half_0_0 : valueIteration salvageMDP (1 / 2) 0 salvageG 0 = 0 := by
  show salvageG 0 = 0
  exact salvageG_0

private theorem salvage_VI_half_0_1 : valueIteration salvageMDP (1 / 2) 0 salvageG 1 = 4 := by
  show salvageG 1 = 4
  exact salvageG_1

private theorem salvage_q_zero_g_00 : qValue salvageMDP 0 salvageG 0 0 = 1 := by
  unfold qValue
  show salvageReward 0 0 + 0 * ∑ s', salvageProb 0 0 s' * salvageG s' = 1
  rw [salvageReward_00]
  simp

private theorem salvage_q_zero_g_01 : qValue salvageMDP 0 salvageG 0 1 = 0 := by
  unfold qValue
  show salvageReward 0 1 + 0 * ∑ s', salvageProb 0 1 s' * salvageG s' = 0
  rw [salvageReward_01]
  simp

private theorem salvage_q_zero_g_10 : qValue salvageMDP 0 salvageG 1 0 = 0 := by
  unfold qValue
  show salvageReward 1 0 + 0 * ∑ s', salvageProb 1 0 s' * salvageG s' = 0
  rw [salvageReward_10]
  simp

private theorem salvage_q_zero_g_11 : qValue salvageMDP 0 salvageG 1 1 = 0 := by
  unfold qValue
  show salvageReward 1 1 + 0 * ∑ s', salvageProb 1 1 s' * salvageG s' = 0
  rw [salvageReward_11]
  simp

private theorem salvage_VI_zero_1_0 : valueIteration salvageMDP 0 1 salvageG 0 = 1 := by
  show bellman salvageMDP 0 salvageG 0 = 1
  unfold bellman
  exact fin2_sup'_eq (by rw [salvage_q_zero_g_00])
    (by rw [salvage_q_zero_g_01]; norm_num) 0 salvage_q_zero_g_00

private theorem salvage_VI_zero_1_1 : valueIteration salvageMDP 0 1 salvageG 1 = 0 := by
  show bellman salvageMDP 0 salvageG 1 = 0
  unfold bellman
  exact fin2_sup'_eq (by rw [salvage_q_zero_g_10])
    (by rw [salvage_q_zero_g_11]) 0 salvage_q_zero_g_10

private theorem salvage_q_one_g_00 : qValue salvageMDP 1 salvageG 0 0 = 1 := by
  unfold qValue
  show salvageReward 0 0 + 1 * ∑ s', salvageProb 0 0 s' * salvageG s' = 1
  rw [Fin.sum_univ_two, salvageProb_000, salvageProb_001, salvageG_0, salvageG_1,
    salvageReward_00]
  ring

private theorem salvage_q_one_g_01 : qValue salvageMDP 1 salvageG 0 1 = 4 := by
  unfold qValue
  show salvageReward 0 1 + 1 * ∑ s', salvageProb 0 1 s' * salvageG s' = 4
  rw [Fin.sum_univ_two, salvageProb_010, salvageProb_011, salvageG_0, salvageG_1,
    salvageReward_01]
  ring

private theorem salvage_q_one_g_10 : qValue salvageMDP 1 salvageG 1 0 = 4 := by
  unfold qValue
  show salvageReward 1 0 + 1 * ∑ s', salvageProb 1 0 s' * salvageG s' = 4
  rw [Fin.sum_univ_two, salvageProb_100, salvageProb_101, salvageG_0, salvageG_1,
    salvageReward_10]
  ring

private theorem salvage_q_one_g_11 : qValue salvageMDP 1 salvageG 1 1 = 4 := by
  unfold qValue
  show salvageReward 1 1 + 1 * ∑ s', salvageProb 1 1 s' * salvageG s' = 4
  rw [Fin.sum_univ_two, salvageProb_110, salvageProb_111, salvageG_0, salvageG_1,
    salvageReward_11]
  ring

private theorem salvage_VI_one_1_0 : valueIteration salvageMDP 1 1 salvageG 0 = 4 := by
  show bellman salvageMDP 1 salvageG 0 = 4
  unfold bellman
  exact fin2_sup'_eq (by rw [salvage_q_one_g_00]; norm_num)
    (by rw [salvage_q_one_g_01]) 1 salvage_q_one_g_01

private theorem salvage_VI_one_1_1 : valueIteration salvageMDP 1 1 salvageG 1 = 4 := by
  show bellman salvageMDP 1 salvageG 1 = 4
  unfold bellman
  exact fin2_sup'_eq (by rw [salvage_q_one_g_10])
    (by rw [salvage_q_one_g_11]) 0 salvage_q_one_g_10

private theorem salvage_naive_fails_0 :
    finiteHorizonValue salvageMDP (1 / 2) 1 0 + salvageG 0
      ≠ valueIteration salvageMDP (1 / 2) 1 salvageG 0 := by
  rw [salvage_FHV_half_1_0, salvageG_0, salvage_VI_half_1_0]
  norm_num

private theorem salvage_naive_fails_1 :
    finiteHorizonValue salvageMDP (1 / 2) 1 1 + salvageG 1
      ≠ valueIteration salvageMDP (1 / 2) 1 salvageG 1 := by
  rw [salvage_FHV_half_1_1, salvageG_1, salvage_VI_half_1_1]
  norm_num

private def costReward (s a : Fin 2) : ℝ :=
  if s = 0 then (if a = 0 then -1 else -3) else 0

private def costMDP : MDP (Fin 2) (Fin 2) ℝ where
  reward := costReward
  prob := salvageProb

private def costG : Fin 2 → ℝ := fun s => if s = 0 then -8 else 0

private theorem costReward_00 : costReward 0 0 = -1 := by
  unfold costReward
  simp

private theorem costReward_01 : costReward 0 1 = -3 := by
  unfold costReward
  simp

private theorem costReward_10 : costReward 1 0 = 0 := by
  unfold costReward
  simp

private theorem costReward_11 : costReward 1 1 = 0 := by
  unfold costReward
  simp

private theorem costG_0 : costG 0 = -8 := by
  unfold costG
  simp

private theorem costG_1 : costG 1 = 0 := by
  unfold costG
  simp

private theorem costMDP_stochastic : costMDP.Stochastic := by
  constructor
  · intro s a s'
    fin_cases s <;> fin_cases a <;> fin_cases s' <;> simp [costMDP, salvageProb]
  · intro s a
    fin_cases s <;> fin_cases a
    · rw [Fin.sum_univ_two]
      show costMDP.prob 0 0 0 + costMDP.prob 0 0 1 = 1
      have h0 : costMDP.prob 0 0 0 = 1 := salvageProb_000
      have h1 : costMDP.prob 0 0 1 = 0 := salvageProb_001
      rw [h0, h1]
      ring
    · rw [Fin.sum_univ_two]
      show costMDP.prob 0 1 0 + costMDP.prob 0 1 1 = 1
      have h0 : costMDP.prob 0 1 0 = 0 := salvageProb_010
      have h1 : costMDP.prob 0 1 1 = 1 := salvageProb_011
      rw [h0, h1]
      ring
    · rw [Fin.sum_univ_two]
      show costMDP.prob 1 0 0 + costMDP.prob 1 0 1 = 1
      have h0 : costMDP.prob 1 0 0 = 0 := salvageProb_100
      have h1 : costMDP.prob 1 0 1 = 1 := salvageProb_101
      rw [h0, h1]
      ring
    · rw [Fin.sum_univ_two]
      show costMDP.prob 1 1 0 + costMDP.prob 1 1 1 = 1
      have h0 : costMDP.prob 1 1 0 = 0 := salvageProb_110
      have h1 : costMDP.prob 1 1 1 = 1 := salvageProb_111
      rw [h0, h1]
      ring

private theorem cost_q_one_00 : qValue costMDP 1 costG 0 0 = -9 := by
  unfold qValue
  show costReward 0 0 + 1 * ∑ s', salvageProb 0 0 s' * costG s' = -9
  rw [Fin.sum_univ_two, salvageProb_000, salvageProb_001, costG_0, costG_1,
    costReward_00]
  ring

private theorem cost_q_one_01 : qValue costMDP 1 costG 0 1 = -3 := by
  unfold qValue
  show costReward 0 1 + 1 * ∑ s', salvageProb 0 1 s' * costG s' = -3
  rw [Fin.sum_univ_two, salvageProb_010, salvageProb_011, costG_0, costG_1,
    costReward_01]
  ring

private theorem cost_q_one_10 : qValue costMDP 1 costG 1 0 = 0 := by
  unfold qValue
  show costReward 1 0 + 1 * ∑ s', salvageProb 1 0 s' * costG s' = 0
  rw [Fin.sum_univ_two, salvageProb_100, salvageProb_101, costG_0, costG_1,
    costReward_10]
  ring

private theorem cost_q_one_11 : qValue costMDP 1 costG 1 1 = 0 := by
  unfold qValue
  show costReward 1 1 + 1 * ∑ s', salvageProb 1 1 s' * costG s' = 0
  rw [Fin.sum_univ_two, salvageProb_110, salvageProb_111, costG_0, costG_1,
    costReward_11]
  ring

private theorem cost_VI_one_1_0 : valueIteration costMDP 1 1 costG 0 = -3 := by
  show bellman costMDP 1 costG 0 = -3
  unfold bellman
  exact fin2_sup'_eq (by rw [cost_q_one_00]; norm_num)
    (by rw [cost_q_one_01]) 1 cost_q_one_01

private theorem cost_VI_one_1_1 : valueIteration costMDP 1 1 costG 1 = 0 := by
  show bellman costMDP 1 costG 1 = 0
  unfold bellman
  exact fin2_sup'_eq (by rw [cost_q_one_10])
    (by rw [cost_q_one_11]) 0 cost_q_one_10

private def pi_const0 : ℕ → Fin 2 → Fin 2 := fun _ _ => 0

private theorem terminal_const0_half_g_1_0 :
    finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) salvageG pi_const0 1 0 = 1 := by
  show qValue salvageMDP (1 / 2) salvageG 0 0 = 1
  exact salvage_q_half_g_00

private theorem terminal_const0_half_g_1_1 :
    finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) salvageG pi_const0 1 1 = 2 := by
  show qValue salvageMDP (1 / 2) salvageG 1 0 = 2
  exact salvage_q_half_g_10

private theorem policy_const0_half_1_0 :
    finiteHorizonPolicyValue salvageMDP (1 / 2) pi_const0 1 0 = 1 := by
  show qValue salvageMDP (1 / 2) (fun _ => 0) 0 0 = 1
  exact salvage_q_half_zero_00

private theorem terminal_const0_zero_agrees_1_0 :
    finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) (fun _ => 0) pi_const0 1 0
      = finiteHorizonPolicyValue salvageMDP (1 / 2) pi_const0 1 0 :=
  finiteHorizonPolicyValueTerminal_agrees_zero salvageMDP (1 / 2) pi_const0 1 0

private theorem terminal_zero_eq_zero :
    finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) (fun _ => 0) pi_const0 0 = fun _ => 0 :=
  finiteHorizonPolicyValueTerminal_zero salvageMDP (1 / 2) (fun _ => 0) pi_const0

private theorem terminal_succ_eq_q :
    finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) salvageG pi_const0 1
      = fun s => qValue salvageMDP (1 / 2)
        (finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) salvageG pi_const0 0) s
        (pi_const0 1 s) :=
  finiteHorizonPolicyValueTerminal_succ salvageMDP (1 / 2) salvageG pi_const0 0

private theorem terminal_le_value_salvage :
    finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) salvageG pi_const0 1 0
      ≤ valueIteration salvageMDP (1 / 2) 1 salvageG 0 :=
  finiteHorizonPolicyValueTerminal_le_valueIteration salvageMDP (1 / 2) salvageG
    salvageMDP_stochastic (by norm_num) pi_const0 1 0

private theorem terminal_le_value_concrete : (1 : ℝ) ≤ 2 := by norm_num

private theorem exists_optimal_salvage :
    ∃ π : ℕ → Fin 2 → Fin 2,
      (∀ (k : ℕ) (s : Fin 2),
        finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) salvageG π k s
          = valueIteration salvageMDP (1 / 2) k salvageG s) ∧
      finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) salvageG π 1 0 = 2 ∧
      finiteHorizonPolicyValueTerminal salvageMDP (1 / 2) salvageG π 1 1 = 2 := by
  obtain ⟨π, h_eq, _⟩ := exists_finiteHorizonTerminalOptimalPolicy salvageMDP (1 / 2)
    salvageG salvageMDP_stochastic (by norm_num)
  refine ⟨π, h_eq, ?_, ?_⟩
  · rw [h_eq 1 0, salvage_VI_half_1_0]
  · rw [h_eq 1 1, salvage_VI_half_1_1]

private def negReward (_ : Fin 2) (a : Fin 2) : ℝ :=
  if a = 0 then 0 else 1

private def negProb (s : Fin 2) (_ : Fin 2) (s' : Fin 2) : ℝ :=
  if s' = s then 1 else 0

private def negMDP : MDP (Fin 2) (Fin 2) ℝ where
  reward := negReward
  prob := negProb

private theorem negReward_0 : ∀ s : Fin 2, negReward s 0 = 0 := by
  intro s
  unfold negReward
  simp

private theorem negReward_1 : ∀ s : Fin 2, negReward s 1 = 1 := by
  intro s
  unfold negReward
  simp

private theorem negProb_self_0 : ∀ a : Fin 2, negProb 0 a 0 = 1 := by
  intro a
  unfold negProb
  simp

private theorem negProb_other_01 : ∀ a : Fin 2, negProb 0 a 1 = 0 := by
  intro a
  unfold negProb
  simp

private theorem negProb_other_10 : ∀ a : Fin 2, negProb 1 a 0 = 0 := by
  intro a
  unfold negProb
  simp

private theorem negProb_self_1 : ∀ a : Fin 2, negProb 1 a 1 = 1 := by
  intro a
  unfold negProb
  simp

private theorem negMDP_stochastic : negMDP.Stochastic := by
  constructor
  · intro s a s'
    fin_cases s <;> fin_cases a <;> fin_cases s' <;> simp [negMDP, negProb]
  · intro s a
    fin_cases s <;> fin_cases a
    · rw [Fin.sum_univ_two]
      show negMDP.prob 0 0 0 + negMDP.prob 0 0 1 = 1
      have h0 : negMDP.prob 0 0 0 = 1 := negProb_self_0 0
      have h1 : negMDP.prob 0 0 1 = 0 := negProb_other_01 0
      rw [h0, h1]
      ring
    · rw [Fin.sum_univ_two]
      show negMDP.prob 0 1 0 + negMDP.prob 0 1 1 = 1
      have h0 : negMDP.prob 0 1 0 = 1 := negProb_self_0 1
      have h1 : negMDP.prob 0 1 1 = 0 := negProb_other_01 1
      rw [h0, h1]
      ring
    · rw [Fin.sum_univ_two]
      show negMDP.prob 1 0 0 + negMDP.prob 1 0 1 = 1
      have h0 : negMDP.prob 1 0 0 = 0 := negProb_other_10 0
      have h1 : negMDP.prob 1 0 1 = 1 := negProb_self_1 0
      rw [h0, h1]
      ring
    · rw [Fin.sum_univ_two]
      show negMDP.prob 1 1 0 + negMDP.prob 1 1 1 = 1
      have h0 : negMDP.prob 1 1 0 = 0 := negProb_other_10 1
      have h1 : negMDP.prob 1 1 1 = 1 := negProb_self_1 1
      rw [h0, h1]
      ring

private theorem neg_q_zero_00 : qValue negMDP (-1) (fun _ => 0) 0 0 = 0 := by
  unfold qValue
  show negReward 0 0 + -1 * ∑ s', negProb 0 0 s' * (0 : ℝ) = 0
  rw [negReward_0 0]
  simp

private theorem neg_q_zero_01 : qValue negMDP (-1) (fun _ => 0) 0 1 = 1 := by
  unfold qValue
  show negReward 0 1 + -1 * ∑ s', negProb 0 1 s' * (0 : ℝ) = 1
  rw [negReward_1 0]
  simp

private theorem neg_q_zero_10 : qValue negMDP (-1) (fun _ => 0) 1 0 = 0 := by
  unfold qValue
  show negReward 1 0 + -1 * ∑ s', negProb 1 0 s' * (0 : ℝ) = 0
  rw [negReward_0 1]
  simp

private theorem neg_q_zero_11 : qValue negMDP (-1) (fun _ => 0) 1 1 = 1 := by
  unfold qValue
  show negReward 1 1 + -1 * ∑ s', negProb 1 1 s' * (0 : ℝ) = 1
  rw [negReward_1 1]
  simp

private theorem neg_VI_1_0 : valueIteration negMDP (-1) 1 (fun _ => 0) 0 = 1 := by
  show bellman negMDP (-1) (fun _ => 0) 0 = 1
  unfold bellman
  exact fin2_sup'_eq (by rw [neg_q_zero_00]; norm_num)
    (by rw [neg_q_zero_01]) 1 neg_q_zero_01

private theorem neg_VI_1_1 : valueIteration negMDP (-1) 1 (fun _ => 0) 1 = 1 := by
  show bellman negMDP (-1) (fun _ => 0) 1 = 1
  unfold bellman
  exact fin2_sup'_eq (by rw [neg_q_zero_10]; norm_num)
    (by rw [neg_q_zero_11]) 1 neg_q_zero_11

private theorem neg_VI_1_eq_one : valueIteration negMDP (-1) 1 (fun _ => 0) = fun _ => 1 := by
  funext s
  fin_cases s
  · exact neg_VI_1_0
  · exact neg_VI_1_1

private theorem neg_q_one_00 : qValue negMDP (-1) (fun _ => 1) 0 0 = -1 := by
  unfold qValue
  show negReward 0 0 + -1 * ∑ s', negProb 0 0 s' * (1 : ℝ) = -1
  rw [Fin.sum_univ_two, negProb_self_0, negProb_other_01, negReward_0]
  ring

private theorem neg_q_one_01 : qValue negMDP (-1) (fun _ => 1) 0 1 = 0 := by
  unfold qValue
  show negReward 0 1 + -1 * ∑ s', negProb 0 1 s' * (1 : ℝ) = 0
  rw [Fin.sum_univ_two, negProb_self_0, negProb_other_01, negReward_1]
  ring

private theorem neg_q_one_10 : qValue negMDP (-1) (fun _ => 1) 1 0 = -1 := by
  unfold qValue
  show negReward 1 0 + -1 * ∑ s', negProb 1 0 s' * (1 : ℝ) = -1
  rw [Fin.sum_univ_two, negProb_other_10, negProb_self_1, negReward_0]
  ring

private theorem neg_q_one_11 : qValue negMDP (-1) (fun _ => 1) 1 1 = 0 := by
  unfold qValue
  show negReward 1 1 + -1 * ∑ s', negProb 1 1 s' * (1 : ℝ) = 0
  rw [Fin.sum_univ_two, negProb_other_10, negProb_self_1, negReward_1]
  ring

private theorem neg_VI_2_0 : valueIteration negMDP (-1) 2 (fun _ => 0) 0 = 0 := by
  have hVI : valueIteration negMDP (-1) 2 (fun _ => 0)
      = bellman negMDP (-1) (valueIteration negMDP (-1) 1 (fun _ => 0)) :=
    Function.iterate_succ_apply' (bellman negMDP (-1)) 1 (fun _ => 0)
  rw [hVI, neg_VI_1_eq_one]
  show bellman negMDP (-1) (fun _ => 1) 0 = 0
  unfold bellman
  exact fin2_sup'_eq (by rw [neg_q_one_00]; norm_num)
    (by rw [neg_q_one_01]) 1 neg_q_one_01

private theorem neg_VI_2_1 : valueIteration negMDP (-1) 2 (fun _ => 0) 1 = 0 := by
  have hVI : valueIteration negMDP (-1) 2 (fun _ => 0)
      = bellman negMDP (-1) (valueIteration negMDP (-1) 1 (fun _ => 0)) :=
    Function.iterate_succ_apply' (bellman negMDP (-1)) 1 (fun _ => 0)
  rw [hVI, neg_VI_1_eq_one]
  show bellman negMDP (-1) (fun _ => 1) 1 = 0
  unfold bellman
  exact fin2_sup'_eq (by rw [neg_q_one_10]; norm_num)
    (by rw [neg_q_one_11]) 1 neg_q_one_11

private def pi_neg : ℕ → Fin 2 → Fin 2 := fun k _ => if k = 2 then 1 else 0

private theorem pi_neg_1 : ∀ s : Fin 2, pi_neg 1 s = 0 := by
  intro s
  simp [pi_neg]

private theorem pi_neg_2 : ∀ s : Fin 2, pi_neg 2 s = 1 := by
  intro s
  simp [pi_neg]

private theorem neg_terminal_1_0 :
    finiteHorizonPolicyValueTerminal negMDP (-1) (fun _ => 0) pi_neg 1 0 = 0 := by
  have hpi : pi_neg 1 0 = 0 := pi_neg_1 0
  show qValue negMDP (-1) (fun _ => 0) 0 (pi_neg 1 0) = 0
  rw [hpi]
  exact neg_q_zero_00

private theorem neg_terminal_1_1 :
    finiteHorizonPolicyValueTerminal negMDP (-1) (fun _ => 0) pi_neg 1 1 = 0 := by
  have hpi : pi_neg 1 1 = 0 := pi_neg_1 1
  show qValue negMDP (-1) (fun _ => 0) 1 (pi_neg 1 1) = 0
  rw [hpi]
  exact neg_q_zero_10

private theorem neg_terminal_1_eq_zero :
    finiteHorizonPolicyValueTerminal negMDP (-1) (fun _ => 0) pi_neg 1 = fun _ => 0 := by
  funext s
  fin_cases s
  · exact neg_terminal_1_0
  · exact neg_terminal_1_1

private theorem neg_terminal_2_0 :
    finiteHorizonPolicyValueTerminal negMDP (-1) (fun _ => 0) pi_neg 2 0 = 1 := by
  have hpi : pi_neg 2 0 = 1 := pi_neg_2 0
  have hfun := neg_terminal_1_eq_zero
  show qValue negMDP (-1)
    (finiteHorizonPolicyValueTerminal negMDP (-1) (fun _ => 0) pi_neg 1) 0 (pi_neg 2 0) = 1
  rw [hfun, hpi]
  exact neg_q_zero_01

private theorem neg_terminal_2_1 :
    finiteHorizonPolicyValueTerminal negMDP (-1) (fun _ => 0) pi_neg 2 1 = 1 := by
  have hpi : pi_neg 2 1 = 1 := pi_neg_2 1
  have hfun := neg_terminal_1_eq_zero
  show qValue negMDP (-1)
    (finiteHorizonPolicyValueTerminal negMDP (-1) (fun _ => 0) pi_neg 1) 1 (pi_neg 2 1) = 1
  rw [hfun, hpi]
  exact neg_q_zero_11

private theorem neg_gamma_counterexample_0 :
    valueIteration negMDP (-1) 2 (fun _ => 0) 0
      < finiteHorizonPolicyValueTerminal negMDP (-1) (fun _ => 0) pi_neg 2 0 := by
  rw [neg_VI_2_0, neg_terminal_2_0]
  norm_num

private theorem neg_gamma_counterexample_1 :
    valueIteration negMDP (-1) 2 (fun _ => 0) 1
      < finiteHorizonPolicyValueTerminal negMDP (-1) (fun _ => 0) pi_neg 2 1 := by
  rw [neg_VI_2_1, neg_terminal_2_1]
  norm_num



end FiniteHorizon

end Cslib.Algorithms.Lean.MarkovDecision
