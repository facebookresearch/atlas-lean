/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.StochasticPolicy
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Stochastic policy, occupancy and performance difference tests

Closed checks over `ℝ` on a two-state, two-action MDP with `γ = 1/2`: the hypotheses of the main
theorems are satisfiable (row-stochastic transitions, a uniform and a deterministic policy, an
initial distribution), the occupancy measure is a probability distribution, the deterministic
embedding agrees with `policyValue`, the performance difference lemma instantiates, and a
constant reward has the value `1 / (1 - γ) = 2`. The boundary `γ = 1` is excluded: the Bellman
equation of the constant reward `1` then has no solution.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

private abbrev St := Fin 2
private abbrev Ac := Fin 2

/-- Two states, two actions; action `0` tends to stay, action `1` tends to switch. -/
private noncomputable def toy : MDP St Ac ℝ where
  reward := ![![1, 0], ![0, 2]]
  prob := ![![![3/4, 1/4], ![1/4, 3/4]], ![![1/2, 1/2], ![1, 0]]]

private theorem toy_stochastic : toy.Stochastic := by
  refine ⟨fun s a s' => ?_, fun s a => ?_⟩ <;> fin_cases s <;> fin_cases a <;>
    (try fin_cases s') <;> norm_num [toy, Fin.sum_univ_two]

private noncomputable def uniform : St → Ac → ℝ := fun _ _ => 1 / 2

private theorem uniform_stochastic : IsRowStochastic uniform :=
  ⟨fun _ _ => by norm_num [uniform], fun _ => by norm_num [uniform, Fin.sum_univ_two]⟩

private noncomputable def start : St → ℝ := ![1, 0]

private theorem start_sum : ∑ s, start s = 1 := by simp [start, Fin.sum_univ_two]

private theorem start_nonneg : ∀ s, 0 ≤ start s := by
  intro s; fin_cases s <;> simp [start]

private theorem hγ0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
private theorem hγ1 : (1 / 2 : ℝ) < 1 := by norm_num

/-- The occupancy measure of the uniform policy from state `0` sums to `1`. -/
example : ∑ p : St × Ac, occupancy toy (1 / 2) toy_stochastic hγ0 hγ1 uniform uniform_stochastic
    start p = 1 :=
  sum_occupancy toy_stochastic hγ0 hγ1 uniform_stochastic start_sum

example (p : St × Ac) :
    0 ≤ occupancy toy (1 / 2) toy_stochastic hγ0 hγ1 uniform uniform_stochastic start p :=
  occupancy_nonneg toy_stochastic hγ0 hγ1 uniform_stochastic start_nonneg p

/-- The deterministic embedding: playing action `1` everywhere. -/
example : stochPolicyValue toy (1 / 2) toy_stochastic hγ0 hγ1 (detPolicy fun _ : St => (1 : Ac))
    (isRowStochastic_detPolicy _) = policyValue toy (1 / 2) toy_stochastic hγ0 hγ1 fun _ => 1 :=
  stochPolicyValue_detPolicy toy_stochastic hγ0 hγ1 _

/-- The performance difference lemma, comparing the uniform policy with "always action `1`". -/
example :
    ∑ s, start s * stochPolicyValue toy (1 / 2) toy_stochastic hγ0 hγ1 uniform
        uniform_stochastic s -
      ∑ s, start s * stochPolicyValue toy (1 / 2) toy_stochastic hγ0 hγ1
        (detPolicy fun _ : St => (1 : Ac)) (isRowStochastic_detPolicy _) s =
      (1 - 1 / 2)⁻¹ * ∑ p : St × Ac,
        occupancy toy (1 / 2) toy_stochastic hγ0 hγ1 uniform uniform_stochastic start p *
          advantage toy (1 / 2) toy_stochastic hγ0 hγ1 (detPolicy fun _ : St => (1 : Ac))
            (isRowStochastic_detPolicy _) p :=
  performance_difference toy_stochastic hγ0 hγ1 (isRowStochastic_detPolicy _)
    uniform_stochastic start

/-- A constant reward `1` has the value `1 / (1 - 1/2) = 2` in every state. -/
example (s : St) :
    chainValue (stateKernel toy uniform)
      (isRowStochastic_stateKernel toy_stochastic uniform_stochastic) (1 / 2) hγ0 hγ1
      (fun _ => 1) s = 2 := by
  rw [chainValue_const]
  norm_num

/-- `γ = 1` is excluded: the Bellman equation `V = 1 + γ V` of the constant reward `1` has no
solution. -/
example : ¬ ∃ V : ℝ, V = 1 + 1 * V := by
  rintro ⟨V, hV⟩
  linarith

end Cslib.Algorithms.Lean.MarkovDecision
