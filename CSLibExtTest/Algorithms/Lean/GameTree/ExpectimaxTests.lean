/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.GameTree.Expectimax
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Expectimax tests

Concrete chance-tree values (including negative max and min choices, so the
empty-list totalization cannot hide a wrong maximum), the two-step coin value,
well-formedness and no-opponent-node facts for MDP unfoldings, and the bridge
to `finiteHorizonValue` on the two-state MDP used by the finite-horizon tests.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.ExpectimaxTest

open Cslib.Algorithms.Lean.GameTree
open Cslib.Algorithms.Lean.MarkovDecision
open Cslib.Algorithms.Lean.MarkovDecision.FiniteHorizon

example : expectimax (.leaf (4 : ℝ)) = 4 := rfl

/-- The ledger's coin value: a fair chance between `0` and `1` is `1 / 2`. -/
example :
    expectimax (.chanceNode [(1 / 2, .leaf (0 : ℝ)), (1 / 2, .leaf (1 : ℝ))]) =
      1 / 2 := by
  norm_num [expectimaxChance]

/-- Negative utilities check that max and min are not totalized toward `0`
on nonempty lists. -/
example : expectimax (.maxNode [.leaf (-2 : ℝ), .leaf (-5 : ℝ)]) = -2 := by
  norm_num [expectimaxMax]

example : expectimax (.minNode [.leaf (-2 : ℝ), .leaf (-5 : ℝ)]) = -5 := by
  norm_num [expectimaxMin]

example : expectimax (.affine (2 : ℝ) (1 / 2) (.leaf (6 : ℝ))) = 5 := by
  norm_num

example : expectimax (.maxNode ([] : List ChanceTree)) = 0 := rfl

example : expectimax (.minNode ([] : List ChanceTree)) = 0 := rfl

example :
    (ChanceTree.chanceNode
      [(1 / 2, ChanceTree.leaf (0 : ℝ)), (1 / 2, ChanceTree.leaf (1 : ℝ))]).WellFormed := by
  refine ChanceTree.WellFormed.chanceNode ?_ ?_ ?_
  · intro pt hpt
    simp at hpt
    rcases hpt with rfl | rfl <;> norm_num
  · norm_num
  · intro pt hpt
    simp at hpt
    rcases hpt with rfl | rfl <;> exact ChanceTree.WellFormed.leaf _

/-- A min node is an opponent node, so it is not a max/chance tree. -/
example : ¬ (ChanceTree.minNode [ChanceTree.leaf (1 : ℝ)]).IsMaxChance := by
  intro h
  cases h

/-- Two-state MDP: stay for reward `1`, move for reward `0`, deterministic
transitions, as in the finite-horizon tests. -/
noncomputable def coinMDP : MDP (Fin 2) (Fin 2) ℝ where
  reward := fun _ a => if a = 0 then 1 else 0
  prob := fun s a s' =>
    if a = 0 then (if s' = s then 1 else 0) else (if s' = s then 0 else 1)

theorem coinMDP_stochastic : coinMDP.Stochastic := by
  constructor
  · intro s a s'
    fin_cases s <;> fin_cases a <;> fin_cases s' <;> simp [coinMDP]
  · intro s a
    fin_cases s <;> fin_cases a <;> simp [coinMDP, Fin.sum_univ_two]

example (k : ℕ) (s : Fin 2) : (unfoldTree coinMDP (1 / 2) k s).WellFormed :=
  unfoldTree_wellFormed coinMDP (1 / 2) coinMDP_stochastic k s

example (k : ℕ) (s : Fin 2) : (unfoldTree coinMDP (1 / 2) k s).IsMaxChance :=
  unfoldTree_isMaxChance coinMDP (1 / 2) k s

example : expectimax (unfoldTree coinMDP (1 / 2) 0 0) = 0 := by
  rw [expectimax_unfoldTree]
  simp [finiteHorizonValue_zero]

theorem coinMDP_value2 : finiteHorizonValue coinMDP (1 / 2) 2 0 = 3 / 2 := by
  have hV1 : finiteHorizonValue coinMDP (1 / 2) 1 = fun _ => 1 := by
    funext s
    have h0 : qValue coinMDP (1 / 2) (fun _ => 0) s 0 = 1 := by
      simp [qValue, coinMDP]
    have h1 : qValue coinMDP (1 / 2) (fun _ => 0) s 1 = 0 := by
      simp [qValue, coinMDP]
    change bellman coinMDP (1 / 2) (fun _ => 0) s = 1
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun a _ => ?_
      fin_cases a
      · exact h0.le
      · exact h1.le.trans (by norm_num)
    · have hle : qValue coinMDP (1 / 2) (fun _ => 0) s 0
          ≤ bellman coinMDP (1 / 2) (fun _ => 0) s :=
        Finset.le_sup' _ (Finset.mem_univ 0)
      rw [h0] at hle
      exact hle
  have hq0 : qValue coinMDP (1 / 2) (finiteHorizonValue coinMDP (1 / 2) 1) 0 0
      = 3 / 2 := by
    rw [hV1]
    simp [qValue, coinMDP]
    norm_num
  have hq1 : qValue coinMDP (1 / 2) (finiteHorizonValue coinMDP (1 / 2) 1) 0 1
      = 1 / 2 := by
    rw [hV1]
    simp [qValue, coinMDP, Fin.sum_univ_two]
  change bellman coinMDP (1 / 2) (finiteHorizonValue coinMDP (1 / 2) 1) 0 = 3 / 2
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun a _ => ?_
    fin_cases a
    · exact hq0.le
    · exact hq1.le.trans (by norm_num)
  · have hle : qValue coinMDP (1 / 2) (finiteHorizonValue coinMDP (1 / 2) 1) 0 0
        ≤ bellman coinMDP (1 / 2) (finiteHorizonValue coinMDP (1 / 2) 1) 0 :=
      Finset.le_sup' _ (Finset.mem_univ 0)
    rw [hq0] at hle
    exact hle

/-- The bridge theorem on the concrete MDP: tree expectimax at horizon `2`
is the finite-horizon value `3 / 2`. -/
example : expectimax (unfoldTree coinMDP (1 / 2) 2 0) = 3 / 2 := by
  rw [expectimax_unfoldTree]
  exact coinMDP_value2

#print axioms expectimax_unfoldTree
#print axioms unfoldTree_wellFormed
#print axioms unfoldTree_isMaxChance
#print axioms expectimaxChance_map
#print axioms le_expectimaxMax_of_mem
#print axioms expectimaxMax_le_of_forall

end Cslib.Algorithms.Lean.ExpectimaxTest
