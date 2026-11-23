/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.StochasticShortestPath
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Stochastic shortest path problems: tests

A two-state SSP with one action: from state `0` the system moves to state `1` with probability
`1/2` and terminates otherwise, at reward `-1` (cost `1`); from state `1` it terminates at once, at
reward `-2`. The unique policy is proper, its value is `(-2, -2)` (cost `2` from either state), and
the hypotheses of the wanted Bellman theorem hold (all policies are proper). A self-loop with
probability `1` gives an improper policy, and the SSP of a discounted MDP has only proper policies,
with the discounted values. A one-state, two-action instance (`stopOrLoop`: terminate or loop at
reward `-1`) satisfies the strong SSP conditions with an improper policy whose total reward is
unbounded below.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

private abbrev St := Fin 2

/-- Two nonterminal states, one action. -/
private noncomputable def chain : MDP St Unit ℝ where
  reward := fun s _ => ![-1, -2] s
  prob := fun s _ s' => ![![0, 1/2], ![0, 0]] s s'

private theorem chain_substochastic : chain.Substochastic := by
  refine ⟨fun s _ s' => ?_, fun s _ => ?_⟩
  · fin_cases s <;> fin_cases s' <;> norm_num [chain]
  · fin_cases s <;> norm_num [chain, Fin.sum_univ_two]

private theorem chain_proper (μ : St → Unit) : chain.Proper μ := by
  intro s
  fin_cases s <;>
    simp [transitionMatrix, sq, Matrix.mul_apply, Fin.sum_univ_two, chain]

/-- The value of the proper policy is `(-2, -2)`: cost `2` from either state. -/
example (μ : St → Unit) : sspValue chain μ = ![-2, -2] := by
  refine (eq_sspValue_of_policyBellman_eq chain_substochastic (chain_proper μ) ?_).symm
  funext s
  fin_cases s <;> norm_num [policyBellman, qValue, chain, Fin.sum_univ_two]

/-- Value iteration from `0` converges to the value. -/
example (μ : St → Unit) :
    Filter.Tendsto (fun k => (policyBellman chain 1 μ)^[k] 0) Filter.atTop
      (nhds (sspValue chain μ)) :=
  tendsto_policyBellman_iterate chain_substochastic (chain_proper μ) 0

/-- The strong SSP conditions of the wanted Bellman theorem hold for `chain`. -/
example : (∃ μ : St → Unit, chain.Proper μ) ∧
    ∀ μ : St → Unit, ¬ chain.Proper μ →
      ∃ s, ¬ BddBelow (Set.range fun N : ℕ => (policyBellman chain 1 μ)^[N] 0 s) :=
  ⟨⟨fun _ => (), chain_proper _⟩, fun μ h => (h (chain_proper μ)).elim⟩

/-- A self-loop with probability `1`: the unique policy is improper. -/
private noncomputable def loop : MDP St Unit ℝ where
  reward := fun _ _ => -1
  prob := fun s _ s' => if s = s' then 1 else 0

example (μ : St → Unit) : ¬ loop.Proper μ := by
  intro h
  have := h 0
  simp [transitionMatrix, sq, Matrix.mul_apply, loop] at this

/-- One state and two actions, both at reward `-1`: action `0` terminates, action `1` loops. The
looping policy is improper with total reward `-N` after `N` stages, so the strong SSP conditions
hold with a non-vacuous improper-policy clause. -/
private noncomputable def stopOrLoop : MDP (Fin 1) (Fin 2) ℝ where
  reward := fun _ _ => -1
  prob := fun _ a _ => if a = 1 then 1 else 0

private theorem stopOrLoop_iterate (μ : Fin 1 → Fin 2) (hμ : μ 0 = 1) (N : ℕ) :
    (policyBellman stopOrLoop 1 μ)^[N] 0 0 = -N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply']
      set f := (policyBellman stopOrLoop 1 μ)^[N] 0 with hf
      have hstep : policyBellman stopOrLoop 1 μ f 0 = -1 + f 0 := by
        simp [policyBellman, qValue, stopOrLoop, hμ]
      rw [hstep, ih]; push_cast; ring

example : (∃ μ : Fin 1 → Fin 2, stopOrLoop.Proper μ) ∧
    ∀ μ : Fin 1 → Fin 2, ¬ stopOrLoop.Proper μ →
      ∃ s, ¬ BddBelow (Set.range fun N : ℕ => (policyBellman stopOrLoop 1 μ)^[N] 0 s) := by
  refine ⟨⟨fun _ => 0, fun s => ?_⟩, fun μ hμ => ⟨0, ?_⟩⟩
  · fin_cases s
    simp [transitionMatrix, stopOrLoop]
  · have h1 : μ 0 = 1 := by
      by_contra h
      have h0 : μ 0 = 0 := by omega
      apply hμ
      intro s
      fin_cases s
      simp [transitionMatrix, stopOrLoop, h0]
    rintro ⟨b, hb⟩
    obtain ⟨N, hN⟩ := exists_nat_gt (-b)
    have := hb ⟨N, rfl⟩
    simp only [stopOrLoop_iterate μ h1] at this
    linarith

/-- The looping policy of `stopOrLoop` is improper. -/
example : ¬ stopOrLoop.Proper fun _ => 1 := by
  intro h
  have := h 0
  simp [transitionMatrix, stopOrLoop] at this

/-- A discounted MDP is an SSP in which every policy is proper, with the same values. -/
example (M : MDP St Unit ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : St → Unit) :
    (M.toSSP γ).Proper μ ∧ sspValue (M.toSSP γ) μ = policyValue M γ hM hγ0 hγ1 μ :=
  ⟨proper_toSSP hM hγ0 hγ1 μ, sspValue_toSSP hM hγ0 hγ1 μ⟩

#print axioms contractingWith_policyBellman_iterate
#print axioms tendsto_policyBellman_iterate
#print axioms policyBellman_sspValue
#print axioms eq_sspValue_of_policyBellman_eq
#print axioms tendsto_sum_pow_mulVec
#print axioms policyKernel_ofDet
#print axioms proper_toSSP
#print axioms sspValue_toSSP

end Cslib.Algorithms.Lean.MarkovDecision
