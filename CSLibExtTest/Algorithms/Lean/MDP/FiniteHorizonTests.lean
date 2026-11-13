/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.FiniteHorizon
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite-horizon Bellman tests

A concrete two-state, two-action MDP (stay for reward `1`, move for reward
`0`, deterministic transitions) with discount `1/2`: the horizon-1 value is
`1` at each state, the horizon-2 value at state `0` is `3/2`, the greedy
policy attains it, the always-move policy earns weakly less, and a
nonstationary policy (move with `2` steps remaining, then stay) earns exactly
`1/2`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MarkovDecision.FiniteHorizon.Test

noncomputable def testMDP : MDP (Fin 2) (Fin 2) ℝ where
  reward := fun _ a => if a = 0 then 1 else 0
  prob := fun s a s' =>
    if a = 0 then (if s' = s then 1 else 0) else (if s' = s then 0 else 1)

theorem testMDP_stochastic : testMDP.Stochastic := by
  constructor
  · intro s a s'
    fin_cases s <;> fin_cases a <;> fin_cases s' <;> simp [testMDP]
  · intro s a
    fin_cases s <;> fin_cases a <;> simp [testMDP, Fin.sum_univ_two]

theorem test_qValue_zero (s : Fin 2) (a : Fin 2) :
    qValue testMDP (1 / 2) (fun _ => 0) s a = testMDP.reward s a := by
  simp [qValue]

theorem test_value1 (s : Fin 2) : finiteHorizonValue testMDP (1 / 2) 1 s = 1 := by
  have h0 : qValue testMDP (1 / 2) (fun _ => 0) s 0 = 1 := by
    rw [test_qValue_zero]
    rfl
  have h1 : qValue testMDP (1 / 2) (fun _ => 0) s 1 = 0 := by
    rw [test_qValue_zero]
    rfl
  change bellman testMDP (1 / 2) (fun _ => 0) s = 1
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun a _ => ?_)
    fin_cases a
    · exact h0.le
    · exact h1.le.trans (by norm_num)
  · have hle : qValue testMDP (1 / 2) (fun _ => 0) s 0
        ≤ bellman testMDP (1 / 2) (fun _ => 0) s :=
      Finset.le_sup' _ (Finset.mem_univ 0)
    rw [h0] at hle
    exact hle

theorem test_value2 : finiteHorizonValue testMDP (1 / 2) 2 0 = 3 / 2 := by
  have hV1 : finiteHorizonValue testMDP (1 / 2) 1 = fun _ => 1 := by
    funext s
    exact test_value1 s
  have hq0 : qValue testMDP (1 / 2) (finiteHorizonValue testMDP (1 / 2) 1) 0 0
      = 3 / 2 := by
    rw [hV1]
    have hr : testMDP.reward 0 0 = 1 := rfl
    have hsum : ∑ s' : Fin 2, testMDP.prob 0 0 s' * (1 : ℝ) = 1 := by
      simp only [mul_one]
      exact testMDP_stochastic.2 0 0
    simp only [qValue, hr, hsum]
    norm_num
  have hq1 : qValue testMDP (1 / 2) (finiteHorizonValue testMDP (1 / 2) 1) 0 1
      = 1 / 2 := by
    rw [hV1]
    have hr : testMDP.reward 0 1 = 0 := rfl
    have hsum : ∑ s' : Fin 2, testMDP.prob 0 1 s' * (1 : ℝ) = 1 := by
      simp only [mul_one]
      exact testMDP_stochastic.2 0 1
    simp only [qValue, hr, hsum]
    norm_num
  change bellman testMDP (1 / 2) (finiteHorizonValue testMDP (1 / 2) 1) 0 = 3 / 2
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun a _ => ?_)
    fin_cases a
    · exact hq0.le
    · exact hq1.le.trans (by norm_num)
  · have hle : qValue testMDP (1 / 2) (finiteHorizonValue testMDP (1 / 2) 1) 0 0
        ≤ bellman testMDP (1 / 2) (finiteHorizonValue testMDP (1 / 2) 1) 0 :=
      Finset.le_sup' _ (Finset.mem_univ 0)
    rw [hq0] at hle
    exact hle

theorem test_greedy_attains :
    finiteHorizonPolicyValue testMDP (1 / 2) (finiteHorizonGreedy testMDP (1 / 2)) 2 0
      = 3 / 2 :=
  (finiteHorizonGreedy_value testMDP (1 / 2) 2 0).trans test_value2

noncomputable def testBad : ℕ → Fin 2 → Fin 2 := fun _ _ => 1

theorem test_bad_le :
    finiteHorizonPolicyValue testMDP (1 / 2) testBad 2 0 ≤ 3 / 2 := by
  have h := finiteHorizonValue_ge_policy testMDP (1 / 2) testMDP_stochastic (by norm_num)
    testBad 2 0
  rw [test_value2] at h
  exact h

/-- A nonstationary policy: move (action `1`) with `2` steps remaining, stay
(action `0`) otherwise. -/
noncomputable def testNonstationary : ℕ → Fin 2 → Fin 2 := fun k _ => if k = 2 then 1 else 0

/-- Exact horizon-2 return of `testNonstationary` from state `0`, computed by
unfolding `finiteHorizonPolicyValue`: move first (reward `0`, go to state `1`),
then stay (reward `1`), so `0 + (1/2) * 1 = 1/2`. Reading the index as elapsed
steps, or shifting it by one, gives `1` or `3/2` instead. -/
theorem test_nonstationary_value :
    finiteHorizonPolicyValue testMDP (1 / 2) testNonstationary 2 0 = 1 / 2 := by
  simp [finiteHorizonPolicyValue, testNonstationary, qValue, testMDP, Fin.sum_univ_two]

end Cslib.Algorithms.Lean.MarkovDecision.FiniteHorizon.Test
