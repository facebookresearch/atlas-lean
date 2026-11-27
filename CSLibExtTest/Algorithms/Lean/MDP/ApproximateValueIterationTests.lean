/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.ApproximateValueIteration
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! # Regressions for approximate value iteration -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

open Filter

private def oneState : MDP Unit Unit ℝ where
  reward _ _ := 0
  prob _ _ _ := 1

private theorem oneState_stochastic : oneState.Stochastic := by
  constructor <;> intros <;> simp [oneState]

private theorem oneState_bellman (v : Unit → ℝ) :
    bellman oneState (1 / 2) v = fun _ => (1 / 2) * v () := by
  ext s
  simp [bellman, qValue, oneState]

private theorem zero_optimal : optimalValue oneState (1 / 2) oneState_stochastic
    (by norm_num) (by norm_num) = 0 := by
  symm
  apply eq_optimalValue_of_bellman_eq
  rw [oneState_bellman]
  funext s
  simp

-- Each update adds 1 after the exact Bellman step. The initial error is 3, not the limit 2.
private noncomputable def trajectory (n : ℕ) (_ : Unit) : ℝ := 2 + (1 / 2 : ℝ) ^ n

private theorem trajectory_step (n : ℕ) :
    dist (bellman oneState (1 / 2) (trajectory n)) (trajectory (n + 1)) ≤ 1 := by
  rw [oneState_bellman, dist_pi_le_iff zero_le_one]
  intro s
  rw [Real.dist_eq]
  change |(1 / 2 : ℝ) * (2 + (1 / 2) ^ n) - (2 + (1 / 2) ^ (n + 1))| ≤ 1
  rw [pow_succ, show (1 / 2 : ℝ) * (2 + (1 / 2) ^ n) -
    (2 + (1 / 2) ^ n * (1 / 2)) = -1 by ring]
  norm_num

private theorem trajectory_bound (n : ℕ) :
    dist (optimalValue oneState (1 / 2) oneState_stochastic (by norm_num) (by norm_num))
      (trajectory n) ≤ 2 + (1 / 2 : ℝ) ^ n := by
  have hinit : dist (0 : Unit → ℝ) (trajectory 0) = 3 := by
    apply le_antisymm
    · rw [dist_pi_le_iff (by norm_num)]
      intro s
      norm_num [Real.dist_eq, trajectory]
    · calc
        (3 : ℝ) = dist ((0 : Unit → ℝ) ()) (trajectory 0 ()) := by
          norm_num [Real.dist_eq, trajectory]
        _ ≤ dist (0 : Unit → ℝ) (trajectory 0) := dist_le_pi_dist _ _ ()
  calc
    _ ≤ (1 / 2 : ℝ) ^ n * dist (optimalValue oneState (1 / 2) oneState_stochastic
        (by norm_num) (by norm_num)) (trajectory 0) +
        (1 - (1 / 2 : ℝ) ^ n) * (1 / (1 - 1 / 2)) :=
      dist_optimalValue_approximateValueIteration_le oneState_stochastic
        (by norm_num) (by norm_num) trajectory_step n
    _ = _ := by rw [zero_optimal, hinit]; ring

example : dist (optimalValue oneState (1 / 2) oneState_stochastic (by norm_num) (by norm_num))
    (trajectory 0) ≤ 3 := by
  have h := trajectory_bound 0
  norm_num at h
  exact h

example : dist (optimalValue oneState (1 / 2) oneState_stochastic (by norm_num) (by norm_num))
    (trajectory 2) ≤ 9 / 4 := by
  have h := trajectory_bound 2
  norm_num at h
  exact h

-- A constant estimate ties the actions; action 1 moves to the zero-reward state.
private def tiedActions : MDP (Fin 2) (Fin 2) ℝ where
  reward s _ := if s = 0 then 1 else 0
  prob _ a s' := if s' = a then 1 else 0

private theorem tiedActions_stochastic : tiedActions.Stochastic := by
  constructor
  · intro s a s'
    simp only [tiedActions]
    split <;> norm_num
  · intro s a
    fin_cases a <;> norm_num [tiedActions, Fin.sum_univ_two]

private def level (n : ℕ) : ℝ := if n % 2 = 0 then 0 else 1
private def estimate (n : ℕ) (_ : Fin 2) : ℝ := level n
private def alternatingPolicy (n : ℕ) (_ : Fin 2) : Fin 2 := if n % 2 = 0 then 0 else 1
private def rewardShift (c : ℝ) (s : Fin 2) : ℝ := tiedActions.reward s 0 + c

private theorem jump_qValue (γ : ℝ) (v : Fin 2 → ℝ) (s a : Fin 2) :
    qValue tiedActions γ v s a = tiedActions.reward s 0 + γ * v a := by
  fin_cases a <;> simp [qValue, tiedActions]

private theorem tie_bellman (γ v : ℝ) (s : Fin 2) :
    bellman tiedActions γ (fun _ => v) s = tiedActions.reward s 0 + γ * v := by
  have hq : qValue tiedActions γ (fun _ => v) s = fun _ => tiedActions.reward s 0 + γ * v :=
    funext (jump_qValue γ (fun _ => v) s)
  unfold bellman
  rw [hq, Finset.sup'_const]

private theorem level_bounds (n : ℕ) : 0 ≤ level n ∧ level n ≤ 1 := by
  unfold level
  split <;> norm_num

private theorem reward_bounds (s : Fin 2) :
    0 ≤ tiedActions.reward s 0 ∧ tiedActions.reward s 0 ≤ 1 := by
  change 0 ≤ (if s = 0 then (1 : ℝ) else 0) ∧ (if s = 0 then (1 : ℝ) else 0) ≤ 1
  split <;> norm_num

private theorem tied_step (n : ℕ) :
    dist (bellman tiedActions (1 / 2) (estimate n)) (estimate (n + 1)) ≤ 3 / 2 := by
  rw [dist_pi_le_iff (by norm_num)]
  intro s
  change dist (bellman tiedActions (1 / 2) (fun _ => level n) s) (level (n + 1)) ≤ 3 / 2
  rw [tie_bellman, Real.dist_eq, abs_le]
  obtain ⟨h₀, h₁⟩ := level_bounds n
  obtain ⟨h₂, h₃⟩ := level_bounds (n + 1)
  obtain ⟨h₄, h₅⟩ := reward_bounds s
  constructor <;> linarith

private theorem tied_greedy (γ : ℝ) (n : ℕ) :
    policyBellman tiedActions γ (alternatingPolicy n) (estimate n) =
      bellman tiedActions γ (estimate n) := by
  funext s
  change qValue tiedActions γ (fun _ => level n) s (alternatingPolicy n s) =
    bellman tiedActions γ (fun _ => level n) s
  rw [tie_bellman, jump_qValue]

private theorem tied_optimal :
    optimalValue tiedActions (1 / 2) tiedActions_stochastic (by norm_num) (by norm_num) =
      rewardShift 1 := by
  symm
  apply eq_optimalValue_of_bellman_eq
  funext s
  unfold bellman
  refine le_antisymm (Finset.sup'_le _ _ fun a _ => ?_) ?_
  · rw [jump_qValue]
    have ha := (reward_bounds a).2
    unfold rewardShift
    linarith
  · calc
      rewardShift 1 s = qValue tiedActions (1 / 2) (rewardShift 1) s 0 := by
        rw [jump_qValue]
        norm_num [rewardShift, tiedActions]
      _ ≤ _ := Finset.le_sup' _ (Finset.mem_univ _)

private theorem constant_policyValue (a : Fin 2) :
    policyValue tiedActions (1 / 2) tiedActions_stochastic (by norm_num) (by norm_num)
      (fun _ => a) = rewardShift (tiedActions.reward a 0) := by
  symm
  apply eq_policyValue_of_policyBellman_eq
  funext s
  unfold policyBellman
  rw [jump_qValue]
  unfold rewardShift
  ring

private noncomputable def halfLoss (n : ℕ) : ℝ :=
  dist (optimalValue tiedActions (1 / 2) tiedActions_stochastic (by norm_num) (by norm_num))
    (policyValue tiedActions (1 / 2) tiedActions_stochastic (by norm_num) (by norm_num)
      (alternatingPolicy n))

-- Both the estimates and the policy losses oscillate. The limit superior still has a bound.
example : limsup halfLoss atTop ≤ 6 ∧ ∀ n, halfLoss n = level n := by
  constructor
  · have h := limsup_dist_optimalValue_policyValue_approximateValueIteration_le
      tiedActions_stochastic (by norm_num) (by norm_num) tied_step (tied_greedy (1 / 2))
    norm_num at h
    exact h
  · intro n
    unfold halfLoss
    rw [tied_optimal]
    by_cases hn : n % 2 = 0
    · have hπ : alternatingPolicy n = fun _ => (0 : Fin 2) := by
        funext s
        simp [alternatingPolicy, hn]
      have hr : tiedActions.reward 0 0 = 1 := by norm_num [tiedActions]
      rw [hπ, constant_policyValue, hr, dist_self]
      simp [level, hn]
    · have hπ : alternatingPolicy n = fun _ => (1 : Fin 2) := by
        funext s
        simp [alternatingPolicy, hn]
      have hr : tiedActions.reward 1 0 = 0 := by norm_num [tiedActions]
      rw [hπ, constant_policyValue, hr]
      simp only [level, ite_eq_right hn]
      have hpoint (s : Fin 2) : dist (rewardShift 1 s) (rewardShift 0 s) = 1 := by
        rw [Real.dist_eq, show rewardShift 1 s - rewardShift 0 s = 1 by unfold rewardShift; ring]
        norm_num
      exact le_antisymm ((dist_pi_le_iff zero_le_one).2 (fun s => (hpoint s).le))
        ((hpoint 0).ge.trans (dist_le_pi_dist _ _ 0))

-- The new finite-time policy-loss bound gives exact optimality at zero discount.
example (n : ℕ) :
    optimalValue tiedActions 0 tiedActions_stochastic (by norm_num) (by norm_num) =
      policyValue tiedActions 0 tiedActions_stochastic (by norm_num) (by norm_num)
        (alternatingPolicy n) := by
  have hstep (k : ℕ) : dist (bellman tiedActions 0 (estimate k)) (estimate (k + 1)) ≤ 1 := by
    rw [dist_pi_le_iff zero_le_one]
    intro s
    change dist (bellman tiedActions 0 (fun _ => level k) s) (level (k + 1)) ≤ 1
    rw [tie_bellman, zero_mul, add_zero, Real.dist_eq, abs_le]
    obtain ⟨h₀, h₁⟩ := reward_bounds s
    obtain ⟨h₂, h₃⟩ := level_bounds (k + 1)
    constructor <;> linarith
  have h := dist_optimalValue_policyValue_approximateValueIteration_le
    tiedActions_stochastic (by norm_num) (by norm_num) hstep (tied_greedy 0) n
  exact dist_le_zero.mp (by simpa only [mul_zero, zero_div, zero_mul] using h)

end Cslib.Algorithms.Lean.MarkovDecision
