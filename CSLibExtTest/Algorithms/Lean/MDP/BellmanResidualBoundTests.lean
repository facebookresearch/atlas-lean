/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.BellmanResidualBound
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Regressions for the statewise Bellman residual bound -/

namespace CSLibExtTest.Algorithms.Lean.MDP.BellmanResidualBound

open Cslib.Algorithms.Lean.MarkovDecision
open Cslib.Algorithms.Lean.MarkovDecision.Simplex (mrpValue eq_mrpValue)

private abbrev State := Fin 2

private def reward (s : State) : ℝ := if s = 0 then 1 else 0

-- The action selects the destination. The immediate reward depends only on the source.
private def jump : MDP State State ℝ where
  reward s _ := reward s
  prob _ a y := if y = a then 1 else 0

private theorem jump_stochastic : jump.Stochastic := by
  refine ⟨?_, ?_⟩
  · intro s a y
    simp only [jump]
    split <;> norm_num
  · intro s a
    simp [jump]

private theorem q_jump (γ : ℝ) (W : State → ℝ) (s a : State) :
    qValue jump γ W s a = reward s + γ * W a := by
  simp [qValue, jump, ite_mul]

private def stayHigh : State → State := fun _ => 0
private def stayLow : State → State := fun _ => 1
private def estimate : State → ℝ := fun _ => 2

private theorem greedy_tie (γ : ℝ) :
    policyBellman jump γ stayLow estimate = bellman jump γ estimate := by
  funext s
  change qValue jump γ estimate s (stayLow s) =
    Finset.univ.sup' Finset.univ_nonempty (qValue jump γ estimate s)
  simp_rw [q_jump, estimate, Finset.sup'_const]

private theorem residual (s : State) :
    |bellman jump (1 / 2) estimate s - estimate s| = 1 - reward s := by
  change |Finset.univ.sup' Finset.univ_nonempty (qValue jump (1 / 2) estimate s) - 2| = _
  simp_rw [q_jump, estimate, Finset.sup'_const]
  fin_cases s <;> norm_num [reward]

private theorem high_value (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    policyValue jump (1 / 2) jump_stochastic h₀ h₁ stayHigh = fun s => reward s + 1 := by
  symm
  apply eq_policyValue_of_policyBellman_eq
  funext s
  norm_num [policyBellman, q_jump, stayHigh, reward]

private theorem high_optimal (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    policyValue jump (1 / 2) jump_stochastic h₀ h₁ stayHigh =
      optimalValue jump (1 / 2) jump_stochastic h₀ h₁ := by
  rw [high_value]
  apply eq_optimalValue_of_bellman_eq
  funext s
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    rw [q_jump]
    fin_cases a <;> norm_num [reward]
  · have h := policyBellman_le_bellman (M := jump) (γ := 1 / 2) stayHigh
      (fun s => reward s + 1) s
    convert h using 1
    change reward s + 1 = qValue jump (1 / 2) (fun s => reward s + 1) s 0
    rw [q_jump]
    norm_num [reward]

private theorem low_value (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    policyValue jump (1 / 2) jump_stochastic h₀ h₁ stayLow = reward := by
  symm
  apply eq_policyValue_of_policyBellman_eq
  funext s
  simp [policyBellman, q_jump, stayLow, reward]

private theorem mrp_jump (a : State) (c : State → ℝ)
    (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    mrpValue (transitionMatrix jump (fun _ => a))
      (transitionMatrix_mem_rowStochastic jump_stochastic (fun _ => a)) h₀ h₁ c =
        fun s => c s + c a := by
  symm
  apply eq_mrpValue
  intro s
  simp only [transitionMatrix, Matrix.of_apply, jump]
  rw [show (∑ y : State, (if y = a then (1 : ℝ) else 0) * (c y + c a)) = c a + c a by
    simp [ite_mul]]
  ring

-- With discount 1/2, jumping to the low-reward state is greedy for the constant estimate
-- but suboptimal. The true loss is one everywhere; the statewise bound is tight at state zero.
example (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    let loss := optimalValue jump (1 / 2) jump_stochastic h₀ h₁ -
      policyValue jump (1 / 2) jump_stochastic h₀ h₁ stayLow
    (∀ s, loss s = 1) ∧ loss 0 ≤ 1 := by
  intro loss
  have hstar := high_optimal h₀ h₁
  have hbound := (optimalValue_sub_policyValue_le_abs_residual jump_stochastic h₀ h₁
    estimate stayLow stayHigh (greedy_tie _) hstar).2 (0 : State)
  change loss 0 ≤
    mrpValue (transitionMatrix jump stayHigh) (transitionMatrix_mem_rowStochastic jump_stochastic
      stayHigh) h₀ h₁ (fun s => |bellman jump (1 / 2) estimate s - estimate s|) 0 +
    mrpValue (transitionMatrix jump stayLow) (transitionMatrix_mem_rowStochastic jump_stochastic
      stayLow) h₀ h₁ (fun s => |bellman jump (1 / 2) estimate s - estimate s|) 0 at hbound
  have hh := congrFun (mrp_jump 0 (fun s => |bellman jump (1 / 2) estimate s - estimate s|)
    h₀ h₁) (0 : State)
  have hl := congrFun (mrp_jump 1 (fun s => |bellman jump (1 / 2) estimate s - estimate s|)
    h₀ h₁) (0 : State)
  change mrpValue (transitionMatrix jump stayHigh) _ h₀ h₁ _ 0 = _ at hh
  change mrpValue (transitionMatrix jump stayLow) _ h₀ h₁ _ 0 = _ at hl
  rw [hh, hl] at hbound
  norm_num [residual, reward] at hbound
  refine ⟨fun s => ?_, hbound⟩
  change optimalValue jump (1 / 2) jump_stochastic h₀ h₁ s -
    policyValue jump (1 / 2) jump_stochastic h₀ h₁ stayLow s = 1
  rw [← hstar, high_value, low_value]
  ring

-- The signed comparison gives zero loss at discount zero even for a nonzero residual.
example {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A ℝ) (hM : M.Stochastic) (W : S → ℝ) (π : S → A)
    (hπ : policyBellman M 0 π W = bellman M 0 W) :
    optimalValue M 0 hM le_rfl zero_lt_one = policyValue M 0 hM le_rfl zero_lt_one π := by
  let πstar := greedy M 0 (optimalValue M 0 hM le_rfl zero_lt_one)
  let e := bellman M 0 W - W
  have h (σ : S → A) : mrpValue (transitionMatrix M σ) (transitionMatrix_mem_rowStochastic hM σ)
      le_rfl zero_lt_one e = e := by
    symm
    apply eq_mrpValue
    intro s
    simp
  have hb := optimalValue_sub_policyValue_le_signed_residual hM le_rfl zero_lt_one W π πstar
    hπ (policyValue_greedy hM le_rfl zero_lt_one)
  change _ ≤ mrpValue (transitionMatrix M πstar) _ le_rfl zero_lt_one e -
    mrpValue (transitionMatrix M π) _ le_rfl zero_lt_one e at hb
  rw [h πstar, h π, sub_self] at hb
  exact sub_eq_zero.mp <| le_antisymm hb
    (sub_nonneg.mpr (policyValue_le_optimalValue hM le_rfl zero_lt_one π))

end CSLibExtTest.Algorithms.Lean.MDP.BellmanResidualBound
