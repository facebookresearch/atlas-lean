/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Finite.Defs

/-!
# Deterministic search problems

Hart, Nilsson and Raphael, *A formal basis for the heuristic determination of minimum cost paths*
(1968), §I.B, describe implicit graphs through a start node, successors with arc costs, and a
set of goals. Here locally applicable actions label the arcs. The model allows zero step costs,
includes the empty solution at a goal, and uses an extended nonnegative infimum rather than
requiring a least-cost solution. No search procedure is specified.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal NNReal

namespace Cslib.Planning.DeterministicSearch

/-- **Deterministic search problem.** On an arbitrary state type, a problem fixes an initial
state, a type of applicable actions at each state, a deterministic successor for each such
state-action pair, a decidable goal predicate, and a finite nonnegative cost for each step. -/
structure Problem (State : Type*) where
  /-- The designated starting state. -/
  initial : State
  /-- The type of actions applicable at the given state. -/
  Action : State → Type*
  /-- The successor obtained by taking an applicable action. -/
  step (s : State) : Action s → State
  /-- The predicate identifying goal states. -/
  goal : State → Prop
  /-- The goal predicate is decidable; applicability need not be decidable. -/
  goalDecidable : DecidablePred goal
  /-- The finite nonnegative cost of taking an applicable action. -/
  stepCost (s : State) : Action s → ℝ≥0

namespace Problem

variable {State : Type*} (P : Problem State)

/-- A finite legal plan from a state: stop there, or take an applicable action and continue
with a plan starting at its successor. -/
inductive Plan : State → Type _ where
  | nil (s : State) : Plan s
  | cons {s : State} (a : P.Action s) (tail : Plan (P.step s a)) : Plan s

variable {P}

/-- The last state reached by a plan, including its starting state for the empty plan. -/
def Plan.endState {s : State} : P.Plan s → State
  | .nil s => s
  | .cons _ tail => tail.endState

/-- The induced finite path of a legal plan, in order from its starting state to its last
state, including both endpoints. -/
def Plan.states {s : State} : P.Plan s → List State
  | .nil s => [s]
  | .cons (s := s) _ tail => s :: tail.states

/-- The sum of the step costs of a plan, zero for the empty plan. The sum is finite and
nonnegative. -/
def Plan.cost {s : State} : P.Plan s → ℝ≥0
  | .nil _ => 0
  | .cons (s := s) a tail => P.stepCost s a + tail.cost

variable (P)

/-- A solution from `s` is a finite legal plan from `s` whose last state satisfies the goal
predicate. The empty plan is a solution exactly at a goal. -/
def Solution (s : State) := {p : P.Plan s // P.goal p.endState}

/-- The optimal cost from `s` is the infimum of the costs of all solutions from `s`, in the
extended nonnegative reals. The infimum of the empty family is infinity, and a finite
infimum need not be attained. -/
noncomputable def optimalCost (s : State) : ℝ≥0∞ :=
  ⨅ p : P.Solution s, (p.1.cost : ℝ≥0∞)

/-- A problem is finitely branching if the type of applicable actions at every state is
finite. The state type need not be finite. -/
def FinitelyBranching : Prop := ∀ s, Finite (P.Action s)

variable {P} {s : State}

/-- The optimal cost is a lower bound for the cost of each solution. -/
theorem optimalCost_le (p : P.Solution s) : P.optimalCost s ≤ (p.1.cost : ℝ≥0∞) :=
  iInf_le _ p

/-- The optimal cost is infinite exactly when there is no solution. -/
theorem optimalCost_eq_top_iff : P.optimalCost s = ⊤ ↔ IsEmpty (P.Solution s) := by
  constructor
  · intro h
    exact ⟨fun p => ENNReal.coe_ne_top (top_le_iff.mp (h ▸ optimalCost_le p))⟩
  · intro h
    let _ : IsEmpty (P.Solution s) := h
    exact iInf_of_empty (fun p : P.Solution s => (p.1.cost : ℝ≥0∞))

/-- At a goal state, the empty solution has cost zero, so the optimal cost is zero. -/
theorem optimalCost_eq_zero_of_goal (h : P.goal s) : P.optimalCost s = 0 :=
  le_antisymm (optimalCost_le (P := P) (s := s) ⟨.nil s, h⟩) bot_le

end Problem

end Cslib.Planning.DeterministicSearch
