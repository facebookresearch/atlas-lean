/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Grim trigger in the repeated prisoner's dilemma: one-shot incentive inequalities

The stage game is the symmetric prisoner's dilemma with payoffs `temptation` (defect against a
cooperator), `reward` (mutual cooperation), `punishment` (mutual defection) and `sucker` (cooperate
against a defector). Grim trigger is the two-state automaton that cooperates in the cooperative
state, defects in the punishment state, and moves to the punishment state forever after any
defection. The stated continuation values are stipulated: `reward` in the cooperative state and
`punishment` in the punishment state, and `value_bellman` shows that they satisfy the Bellman
identity of the strategy for every `δ`. No infinite series is defined here; for a discount factor
`0 ≤ δ < 1` these are the normalized discounted sums `(1 - δ) ∑ₜ δᵗ uₜ` of the constant payoff
streams that grim trigger generates from each state. A one-shot deviation is a single-period
change of action followed by a return to the strategy.

## Main results

* `RepeatedPrisonersDilemma.value_bellman`: the stated continuation values are the values of
  grim trigger.
* `RepeatedPrisonersDilemma.oneShotIncentives_iff`: grim trigger satisfies the one-shot
  incentive inequalities if and only if `T - R ≤ δ (T - P)`, given `S ≤ P` and `δ ≤ 1`.

The one-shot deviation principle (that these inequalities imply subgame perfection) is not
covered.

## References

* D. Abreu, *On the theory of infinitely repeated games with discounting*, Econometrica 56(2)
  (1988), 383–396.
* M. J. Osborne and A. Rubinstein, *A Course in Game Theory*, MIT Press (1994), Chapter 8.
-/

@[expose] public section

namespace MathlibExt.GameTheory.RepeatedPrisonersDilemma

/-- The stage payoffs of a symmetric prisoner's dilemma. -/
structure Payoffs where
  /-- Payoff from defecting against a cooperator. -/
  temptation : ℝ
  /-- Payoff from mutual cooperation. -/
  reward : ℝ
  /-- Payoff from mutual defection. -/
  punishment : ℝ
  /-- Payoff from cooperating against a defector. -/
  sucker : ℝ

/-- A player's stage payoff from their own action `me` and the opponent's action `other`
(`true` = cooperate, `false` = defect). -/
def Payoffs.stage (g : Payoffs) : Bool → Bool → ℝ
  | true, true => g.reward
  | true, false => g.sucker
  | false, true => g.temptation
  | false, false => g.punishment

/-- The states of the grim-trigger automaton. -/
inductive GrimState
  /-- No defection has occurred: cooperate. -/
  | coop
  /-- Some defection has occurred: defect forever. -/
  | punish
  deriving DecidableEq

namespace GrimState

/-- The action prescribed in each state (`true` = cooperate). -/
def action : GrimState → Bool
  | coop => true
  | punish => false

/-- The transition after the stage profile `(a, b)`: stay cooperative only after mutual
cooperation in the cooperative state; the punishment state is absorbing. -/
def next : GrimState → Bool → Bool → GrimState
  | coop, true, true => coop
  | _, _, _ => punish

/-- The stated continuation values of grim trigger played by both players (stipulated; for
`0 ≤ δ < 1` the normalized discounted payoffs): `reward` in the cooperative state,
`punishment` in the punishment state. -/
def value (g : Payoffs) : GrimState → ℝ
  | coop => g.reward
  | punish => g.punishment

end GrimState

open GrimState

/-- The stated continuation values are the values of the strategy: in each state, value =
`(1 - δ) ·` stage payoff of the prescribed profile `+ δ ·` value of the next state. -/
theorem value_bellman (g : Payoffs) (δ : ℝ) (s : GrimState) :
    value g s = (1 - δ) * g.stage s.action s.action + δ * value g (s.next s.action s.action) := by
  cases s <;> simp [value, Payoffs.stage, action, next] <;> ring

/-- The one-shot incentive inequalities of grim trigger: in every state, no single-period
deviation to an action `a'` against the prescribed action of the opponent, followed by a return
to grim trigger from the resulting state, gives a higher normalized value. -/
def OneShotIncentives (g : Payoffs) (δ : ℝ) : Prop :=
  ∀ (s : GrimState) (a' : Bool),
    (1 - δ) * g.stage a' s.action + δ * value g (s.next a' s.action) ≤ value g s

/-- **The one-shot incentive inequalities of grim trigger, in closed form**: if mutual defection
pays at least the sucker payoff (`S ≤ P`) and `δ ≤ 1`, the one-shot incentive inequalities hold
if and only if `temptation - reward ≤ δ (temptation - punishment)`, that is,
`(1 - δ) T + δ P ≤ R`. This is an algebraic equivalence; no lower bound on `δ` is assumed. In
the economic domain (a discount factor `0 ≤ δ < 1` and a prisoner's dilemma, `T > R > P > S`)
it says that grim trigger is unimprovable by one-shot deviations exactly when
`δ ≥ (T - R) / (T - P)`. -/
theorem oneShotIncentives_iff (g : Payoffs) {δ : ℝ} (hPS : g.sucker ≤ g.punishment)
    (hδ1 : δ ≤ 1) :
    OneShotIncentives g δ ↔ g.temptation - g.reward ≤ δ * (g.temptation - g.punishment) := by
  constructor
  · intro h
    have hcf := h coop false
    simp [value, Payoffs.stage, action, next] at hcf
    linarith
  · intro h s a'
    cases s
    · cases a' <;> simp [value, Payoffs.stage, action, next]
      · linarith
      · have heq : (1 - δ) * g.reward + δ * g.reward = g.reward := by ring
        linarith
    · cases a' <;> simp [value, Payoffs.stage, action, next]
      · have heq : (1 - δ) * g.punishment + δ * g.punishment = g.punishment := by ring
        linarith
      · have h1δ : (0:ℝ) ≤ 1 - δ := by linarith
        have hSP : g.sucker - g.punishment ≤ 0 := by linarith
        have hmul : (1 - δ) * (g.sucker - g.punishment) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos h1δ hSP
        linarith

end MathlibExt.GameTheory.RepeatedPrisonersDilemma
