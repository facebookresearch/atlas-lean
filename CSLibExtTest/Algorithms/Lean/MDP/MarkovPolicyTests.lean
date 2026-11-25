/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.MarkovPolicy
public meta import CSLibExt.Algorithms.Lean.MDP.MarkovPolicy
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Markov policies: tests

Executed fixtures over `ℚ` on the maintenance MDP of the value-iteration tests (three states, two
actions, `γ = 9/10`). For several nonstationary Markov policies (alternating, eventually
switching, cycling through decision rules) and terminal values, the run computes `N`-stage values
and checks `nStageValue ≤ (bellman)^[N]` (`nStageValue_le_iterate`), the recursion
`nStageValue_succ`, and the geometric forgetting of the terminal value
(`dist_nStageValue_le`, in the sup norm); it throws otherwise.

A second run enumerates all `8 * 8` two-stage Markov policies and checks that the best two-stage
value is `T^2 V`, attained by one policy in every state (`isGreatest_nStageValue`).

Closed checks over `ℝ`: an alternating policy of an arbitrary stochastic MDP is no better than
optimal, and `isGreatest_markovValue` instantiates.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

private abbrev St := Fin 3
private abbrev Ac := Fin 2

private meta def machine : MDP St Ac ℚ where
  reward := ![![3, 1], ![2, 0], ![-1, -4]]
  prob := ![![![1/2, 1/2, 0], ![1, 0, 0]],
    ![![0, 1/2, 1/2], ![3/4, 1/4, 0]],
    ![![0, 0, 1], ![1/2, 1/2, 0]]]

private meta def γm : ℚ := 9 / 10
private meta def sts : List St := List.finRange 3

private meta def supDist (V W : St → ℚ) : ℚ := sts.foldl (fun m s => max m (abs (V s - W s))) 0

/-- Tabulate a function on the states. -/
private meta def tab (V : St → ℚ) : St → ℚ :=
  let l := sts.map V
  fun s => l.getD s.val 0

#eval do
  let rules : List (St → Ac) := [![0, 0, 0], ![1, 1, 1], ![0, 1, 1], ![1, 0, 1]]
  let policies : List (ℕ → St → Ac) :=
    [fun k => if k % 2 = 0 then ![0, 1, 1] else ![1, 0, 0],
     fun k => if k < 3 then ![1, 1, 1] else ![0, 1, 1],
     fun k => rules.getD (k % rules.length) ![0, 0, 0]]
  let terminals : List (St → ℚ) := [![0, 0, 0], ![10, -5, 3], ![-20, 20, 0]]
  let mut checks := 0
  for π in policies do
    for V in terminals do
      let mut T : St → ℚ := V
      for N in [0:4] do
        let W := tab (nStageValue machine γm π N V)
        unless sts.all fun s => W s ≤ T s do
          throw (IO.userError s!"N-stage value exceeds value iteration at N = {N}")
        let W' := tab (nStageValue machine γm π (N + 1) V)
        let W'' := tab (nStageValue machine γm π N (policyBellman machine γm (π N) V))
        unless sts.all fun s => W' s == W'' s do
          throw (IO.userError s!"nStageValue_succ fails at N = {N}")
        for V' in terminals do
          let D := supDist W (tab (nStageValue machine γm π N V'))
          unless D ≤ γm ^ N * supDist V V' do
            throw (IO.userError s!"terminal value not forgotten at rate γ^N, N = {N}")
        T := tab (bellman machine γm T)
        checks := checks + 1
  IO.println s!"Markov policies: {checks} exact checks passed"

/-- All eight deterministic decision rules of the maintenance MDP. -/
private meta def allRules : List (St → Ac) :=
  (List.finRange 2).flatMap fun a => (List.finRange 2).flatMap fun b =>
    (List.finRange 2).map fun c => ![a, b, c]

-- Finite horizon `N = 2`: the best two-stage value over all `8 * 8` Markov policies is `T^2 V`,
-- attained by one policy in every state at once (`isGreatest_nStageValue`).
#eval do
  let terminals : List (St → ℚ) := [![0, 0, 0], ![10, -5, 3], ![-20, 20, 0]]
  let mut checks := 0
  for V in terminals do
    let T2 := tab (bellman machine γm (tab (bellman machine γm V)))
    let mut attained := false
    for μ0 in allRules do
      for μ1 in allRules do
        let π : ℕ → St → Ac := fun k => if k = 0 then μ0 else μ1
        let W := tab (nStageValue machine γm π 2 V)
        unless sts.all fun s => W s ≤ T2 s do
          throw (IO.userError "a two-stage policy beats T^2 V")
        if sts.all fun s => W s == T2 s then attained := true
        checks := checks + 1
    unless attained do throw (IO.userError "T^2 V is not attained by a Markov policy")
  IO.println s!"finite horizon: {checks} two-stage policies checked against T^2 V"

/-! Closed checks over `ℝ` -/

section Closed

variable (M : MDP St Ac ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- A nonstationary (alternating) policy is no better than optimal. -/
example (μ ν : St → Ac) :
    markovValue M γ (fun k => if k % 2 = 0 then μ else ν) ≤ optimalValue M γ hM hγ0 hγ1 :=
  markovValue_le_optimalValue hM hγ0 hγ1 _

/-- The two-stage value unfolds as `T_{π 0} (T_{π 1} V)`. -/
example (π : ℕ → St → Ac) (V : St → ℝ) :
    nStageValue M γ π 2 V = policyBellman M γ (π 0) (policyBellman M γ (π 1) V) := rfl

example : IsGreatest (Set.range (markovValue M γ)) (optimalValue M γ hM hγ0 hγ1) :=
  isGreatest_markovValue hM hγ0 hγ1

/-- Finite horizon: the dynamic programming policy is optimal over `N` stages. -/
example (N : ℕ) (V : St → ℝ) :
    IsGreatest (Set.range fun π => nStageValue M γ π N V) ((bellman M γ)^[N] V) :=
  isGreatest_nStageValue hM hγ0 N V

end Closed

#print axioms tendsto_nStageValue
#print axioms markovValue_const
#print axioms markovValue_le_optimalValue
#print axioms isGreatest_markovValue
#print axioms isGreatest_nStageValue

end Cslib.Algorithms.Lean.MarkovDecision
