/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.HistoryPolicy
import MathlibExt.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.NormNum

/-! # Regressions for history-dependent randomized policies -/

open scoped ENNReal

namespace Cslib.Algorithms.Lean.MarkovDecision

private def toy : MDP Unit Bool ℝ where
  reward _ a := if a then 1 else 0
  prob _ _ _ := 1

private theorem toy_stochastic : toy.Stochastic := by
  constructor
  · intro s a s'
    simp [toy]
  · intro s a
    simp [toy]

-- The state never changes, but the policy copies the previous action after a fair first draw.
private noncomputable def copyPolicy : HistoryPolicy (fun _ : Unit => Set.univ : Unit → Set Bool) where
  actionLaw
    | 0, _ => PMF.uniformFintype Bool
    | _ + 1, h => PMF.pure h.2.1
  available_mass _ _ _ ha := (ha (Set.mem_univ _)).elim

-- Both prefixes have positive mass and the same last state and time. The same proposed next
-- action has different mass depending only on the action in the prefix.
example :
    (HistoryPolicy.law toy toy_stochastic copyPolicy () 1 ((), true, ())).toReal = 1 / 2 ∧
    (HistoryPolicy.law toy toy_stochastic copyPolicy () 1 ((), false, ())).toReal = 1 / 2 ∧
    (HistoryPolicy.law toy toy_stochastic copyPolicy () 2 (((), true, ()), true, ())).toReal = 1 / 2 ∧
    (HistoryPolicy.law toy toy_stochastic copyPolicy () 2 (((), false, ()), true, ())).toReal = 0 := by
  have hzero : (HistoryPolicy.law toy toy_stochastic copyPolicy () 0 ()).toReal = 1 := by
    rw [HistoryPolicy.law_toReal_apply toy toy_stochastic copyPolicy () 0 ()]
    norm_num [HistoryPolicy.weight, HistoryPolicy.factors, History.origin]
  have hfirst (a : Bool) : (HistoryPolicy.law toy toy_stochastic copyPolicy () 1 ((), a, ())).toReal =
      1 / 2 := by
    rw [HistoryPolicy.law_toReal_apply_succ toy toy_stochastic copyPolicy () 0 () a (), hzero]
    norm_num [copyPolicy, toy, PMF.uniformFintype_apply]
  refine ⟨hfirst true, hfirst false, ?_, ?_⟩
  · rw [HistoryPolicy.law_toReal_apply_succ toy toy_stochastic copyPolicy () 1 ((), true, ())
      true (), hfirst true]
    norm_num [copyPolicy, toy]
  · rw [HistoryPolicy.law_toReal_apply_succ toy toy_stochastic copyPolicy () 1 ((), false, ())
      true (), hfirst false]
    norm_num [copyPolicy, toy, PMF.pure_apply_of_ne]

private noncomputable def twoState : MDP Bool Unit ℝ where
  reward s _ := if s then 6 else 2
  prob _ _ s' := if s' then 1 / 4 else 3 / 4

private theorem twoState_stochastic : twoState.Stochastic := by
  constructor
  · intro s a s'
    cases s' <;> norm_num [twoState]
  · intro s a
    norm_num [twoState, Fintype.sum_bool]

private noncomputable def onlyAction : HistoryPolicy (fun _ : Bool => Set.univ : Bool → Set Unit) where
  actionLaw _ _ := PMF.pure ()
  available_mass _ _ _ ha := (ha (Set.mem_univ _)).elim

private theorem twoState_mass (s s' : Bool) :
    (HistoryPolicy.law twoState twoState_stochastic onlyAction false 1 (s, (), s')).toReal =
      (if s = false then twoState.prob s () s' else 0) := by
  rw [HistoryPolicy.law_toReal_apply_succ twoState twoState_stochastic onlyAction false 0 s () s',
    HistoryPolicy.law_toReal_apply twoState twoState_stochastic onlyAction false 0 s]
  cases s <;> simp [HistoryPolicy.weight, HistoryPolicy.factors, History.origin, History.last,
    onlyAction]

-- The initial state is fixed, and the probability of reaching `true` is not one.
example :
    (HistoryPolicy.law twoState twoState_stochastic onlyAction false 1 (false, (), true)).toReal =
      1 / 4 ∧
    (HistoryPolicy.law twoState twoState_stochastic onlyAction false 1 (true, (), true)).toReal =
      0 := by
  rw [twoState_mass false true, twoState_mass true true]
  norm_num [twoState]

-- The current state pays 2, not the average successor-state reward of 3.
example : HistoryPolicy.expectedReward twoState twoState_stochastic onlyAction false 0 = 2 := by
  change (∑ p : Bool × (Unit × Bool),
    (HistoryPolicy.law twoState twoState_stochastic onlyAction false 1 p).toReal *
      twoState.reward p.1 p.2.1) = 2
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fintype.sum_unique]
  rw [twoState_mass true true, twoState_mass true false,
    twoState_mass false true, twoState_mass false false]
  norm_num [twoState]

private noncomputable def restricted : HistoryPolicy (fun _ : Unit => ({true} : Set Bool)) where
  actionLaw _ _ := PMF.pure true
  available_mass _ _ a ha := PMF.pure_apply_of_ne true a (by simpa using ha)

example : HistoryPolicy.law toy toy_stochastic restricted () 1 ((), false, ()) = 0 := by
  apply HistoryPolicy.law_apply_eq_zero_of_not_legal
  simp [History.Legal]

example : Summable (fun t : ℕ =>
    |(1 / 2 : ℝ) ^ t * HistoryPolicy.expectedReward toy toy_stochastic copyPolicy () t|) := by
  apply HistoryPolicy.summable_abs_discountedReward (C := 1)
  · norm_num
  · norm_num
  · intro s a
    cases a <;> norm_num [toy]

end Cslib.Algorithms.Lean.MarkovDecision
