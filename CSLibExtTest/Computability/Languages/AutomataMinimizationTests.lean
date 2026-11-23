/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Minimization

/-! # Tests for semantic DFA minimization -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.AutomataMinimizationTests

/-- A universal-language DFA with three redundant, unreachable-equivalent states. -/
def redundantUniversalDFA : DFA Bool (Fin 3) where
  step q a := if a then q else (q + 1)
  start := 0
  accept := Set.univ

@[simp]
theorem redundantUniversalDFA_accepts :
    redundantUniversalDFA.accepts = (Set.univ : Language Bool) := by
  ext w
  constructor <;> intro
  · exact Set.mem_univ w
  · trivial

example (x y : List Bool) :
    minimizedState redundantUniversalDFA x = minimizedState redundantUniversalDFA y := by
  rw [minimizedState_eq_iff_stateEquivalent, stateEquivalent_iff]
  intro z
  simp [redundantUniversalDFA]

example :
    (minimizedDFA redundantUniversalDFA).accepts = (Set.univ : Language Bool) := by
  rw [minimizedDFA_accepts, redundantUniversalDFA_accepts]

example : Accessible (minimizedDFA redundantUniversalDFA) :=
  minimizedDFA_accessible redundantUniversalDFA

/-- The two-state recognizer for the language containing only the empty word. -/
def emptyWordDFA : DFA Bool Bool where
  step _ _ := false
  start := true
  accept := {true}

@[simp]
theorem emptyWordDFA_eval_cons (a : Bool) (w : List Bool) :
    emptyWordDFA.eval (a :: w) = false := by
  simp only [DFA.eval, DFA.evalFrom, emptyWordDFA, List.foldl_cons]
  change List.foldl (fun _ _ ↦ false) false w = false
  induction w with
  | nil => rfl
  | cons b w ih => simpa only [List.foldl_cons] using ih

example : minimizedState emptyWordDFA [] ≠ minimizedState emptyWordDFA [true] := by
  intro h
  have hrel : nerodeRel emptyWordDFA.accepts [] [true] :=
    (minimizedState_eq_iff_nerodeRel emptyWordDFA).mp h
  apply (distinguishable_iff_not_nerodeRel.mp ?_) hrel
  refine ⟨[], ?_⟩
  change ¬(true ∈ ({true} : Set Bool) ↔ false ∈ ({true} : Set Bool))
  simp

example (x : List Bool) :
    (leftQuotientEquivReachableResiduals emptyWordDFA).symm
      ((minimizedDFA emptyWordDFA).eval x) = emptyWordDFA.accepts.toDFA.eval x :=
  minimizedDFA_eval_equiv emptyWordDFA x

example (x : List Bool) :
    (minimizedDFA emptyWordDFA).eval x = minimizedState emptyWordDFA x :=
  minimizedDFA_eval emptyWordDFA x

example (x : List Bool) (a : Bool) :
    (minimizedDFA emptyWordDFA).step (minimizedState emptyWordDFA x) a =
      minimizedState emptyWordDFA (x ++ [a]) :=
  minimizedDFA_step_minimizedState emptyWordDFA x a

example (q : reachableResiduals emptyWordDFA) (a : Bool) :
    ((minimizedDFA emptyWordDFA).step q a).val = q.val.leftQuotient [a] :=
  minimizedDFA_step_val emptyWordDFA q a

end Cslib.Language.AutomataMinimizationTests
