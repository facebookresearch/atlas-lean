/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.AverageCost
import MathlibExt.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Tactic.NormNum

/-!
# Tests for the average-cost verification theorem

Instances of `average_cost_verification` on a one-state MDP and on a two-state MDP with random
transitions, for a history-dependent randomized policy and for a stationary policy that attains
the bound.
-/

set_option autoImplicit false

open Filter Topology

namespace Cslib.Algorithms.Lean.MarkovDecision

/-- A history-dependent randomized policy: a uniformly random first action, then the previous
action again. -/
private noncomputable def repeatPolicy {S : Type} :
    HistoryPolicy (fun _ : S => (Set.univ : Set Bool)) where
  actionLaw
    | 0, _ => PMF.uniformFintype Bool
    | _ + 1, x => PMF.pure x.2.1
  available_mass _ _ _ ha := (ha (Set.mem_univ _)).elim

/-- The stationary policy that always plays `false`. -/
private noncomputable def alwaysFalse {S : Type} :
    HistoryPolicy (fun _ : S => (Set.univ : Set Bool)) where
  actionLaw _ _ := PMF.pure false
  available_mass _ _ _ ha := (ha (Set.mem_univ _)).elim

/-- One state and two actions, of costs `1` (`false`) and `3` (`true`). -/
private def oneState : MDP Unit Bool ℝ where
  reward _ a := if a then 3 else 1
  prob _ _ _ := 1

private theorem oneState_stochastic : oneState.Stochastic :=
  ⟨fun _ _ _ => zero_le_one, fun _ _ => by simp [oneState]⟩

/-- In the one-state MDP, `g = 1` and `h = 0` satisfy the inequality. -/
private theorem oneState_le (s : Unit) (a : Bool) :
    1 + (fun _ => (0 : ℝ)) s ≤
      oneState.reward s a + ∑ s', oneState.prob s a s' * (fun _ => 0) s' := by
  cases a <;> norm_num [oneState]

/-- One state: the policy that repeats a uniformly random first action has long-run average cost at
least `1`. -/
example : (1 : ℝ) ≤ liminf (fun N : ℕ =>
    (∑ t ∈ Finset.range N, repeatPolicy.expectedReward oneState oneState_stochastic () t) / N)
      atTop :=
  (average_cost_verification oneState_stochastic oneState_le).1 repeatPolicy ()

/-- One state: always playing the cheaper action attains equality, so its average cost tends to
`1`. -/
example : Tendsto (fun N : ℕ =>
    (∑ t ∈ Finset.range N, alwaysFalse.expectedReward oneState oneState_stochastic () t) / N)
      atTop (𝓝 1) :=
  (average_cost_verification oneState_stochastic oneState_le).2 (fun _ => false)
    (fun _ => by norm_num [oneState]) alwaysFalse (fun _ _ => rfl) ()

/-- Two states and two actions: the next state is uniform whatever the action, state `true` costs
`2` more than state `false`, and action `true` costs `1` more than action `false`. -/
private noncomputable def twoState : MDP Bool Bool ℝ where
  reward s a := (if s then 2 else 0) + (if a then 1 else 0)
  prob _ _ _ := 1 / 2

private theorem twoState_stochastic : twoState.Stochastic :=
  ⟨fun _ _ _ => by norm_num [twoState], fun _ _ => by norm_num [twoState]⟩

/-- In the two-state MDP, `g = 1` and `h = (0, 2)` satisfy the inequality. -/
private theorem twoState_le (s a : Bool) :
    1 + (fun s : Bool => if s then (2 : ℝ) else 0) s ≤
      twoState.reward s a +
        ∑ s', twoState.prob s a s' * (fun s : Bool => if s then 2 else 0) s' := by
  cases s <;> cases a <;> norm_num [twoState]

/-- Two states: every history-dependent policy, here the one that repeats a uniformly random first
action, has long-run average cost at least `1` from either initial state. -/
example (s₀ : Bool) : (1 : ℝ) ≤ liminf (fun N : ℕ =>
    (∑ t ∈ Finset.range N, repeatPolicy.expectedReward twoState twoState_stochastic s₀ t) / N)
      atTop :=
  (average_cost_verification twoState_stochastic twoState_le).1 repeatPolicy s₀

/-- Two states: always playing `false` attains equality, `1 + h s = c(s, false) + ∑ P h`, so the
bound is attained: the average cost tends to `1` from either initial state. -/
example (s₀ : Bool) : Tendsto (fun N : ℕ =>
    (∑ t ∈ Finset.range N, alwaysFalse.expectedReward twoState twoState_stochastic s₀ t) / N)
      atTop (𝓝 1) :=
  (average_cost_verification twoState_stochastic twoState_le).2 (fun _ => false)
    (fun s => by cases s <;> norm_num [twoState]) alwaysFalse (fun _ _ => rfl) s₀

end Cslib.Algorithms.Lean.MarkovDecision
