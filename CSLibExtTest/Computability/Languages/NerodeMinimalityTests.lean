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

public import CSLibExt.Computability.Languages.Congruences.Minimality

/-! # Tests for Nerode distinguishability and DFA minimality -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.NerodeMinimalityTests

/-- The language containing only the empty Boolean word. -/
def emptyOnly : Language Bool := {[]}

example : Distinguishable emptyOnly [] [true] := by
  refine ⟨[], ?_⟩
  unfold emptyOnly
  change ¬([] = [] ↔ [true] = [])
  decide

/-- A two-state recognizer for the language containing only the empty word. -/
def emptyOnlyDFA : DFA Bool Bool where
  step _ _ := false
  start := true
  accept := {true}

@[simp]
theorem emptyOnlyDFA_eval_nil : emptyOnlyDFA.eval [] = true :=
  rfl

@[simp]
theorem emptyOnlyDFA_eval_cons (a : Bool) (w : List Bool) :
    emptyOnlyDFA.eval (a :: w) = false := by
  simp only [DFA.eval, DFA.evalFrom, emptyOnlyDFA, List.foldl_cons]
  change List.foldl (fun _ _ ↦ false) false w = false
  induction w with
  | nil => rfl
  | cons b w ih => simpa only [List.foldl_cons] using ih

@[simp]
theorem emptyOnlyDFA_accepts : emptyOnlyDFA.accepts = emptyOnly := by
  ext w
  cases w with
  | nil =>
      change true ∈ ({true} : Set Bool) ↔ [] ∈ ({[]} : Set (List Bool))
      simp
  | cons a w =>
      rw [DFA.mem_accepts, emptyOnlyDFA_eval_cons]
      change false ∈ ({true} : Set Bool) ↔ a :: w ∈ ({[]} : Set (List Bool))
      simp

example : emptyOnlyDFA.eval [] ≠ emptyOnlyDFA.eval [true] := by
  apply eval_ne_of_distinguishable emptyOnlyDFA emptyOnlyDFA_accepts
  refine ⟨[], ?_⟩
  unfold emptyOnly
  change ¬([] = [] ↔ [true] = [])
  decide

/-- A deliberately redundant recognizer: the states `false` and `true` behave identically. -/
def redundantUniversalDFA : DFA Bool Bool where
  step q _ := q
  start := false
  accept := Set.univ

example : StateEquivalent redundantUniversalDFA false true := by
  apply (stateEquivalent_iff).mpr
  simp [redundantUniversalDFA]

example : reachableResiduals emptyOnlyDFA = Set.range emptyOnly.leftQuotient := by
  rw [reachableResiduals_eq emptyOnlyDFA emptyOnlyDFA_accepts]

/-- The `Nat.card` Myhill-Nerode bound applies to `emptyOnlyDFA` through `[Finite Bool]`. -/
example : Nat.card (Set.range emptyOnly.leftQuotient) ≤ Nat.card Bool :=
  natCard_range_leftQuotient_le_natCard_state emptyOnlyDFA emptyOnlyDFA_accepts

/-- Consequently `emptyOnly` has at most two distinct left quotients. -/
example : Nat.card (Set.range emptyOnly.leftQuotient) ≤ 2 := by
  simpa using natCard_range_leftQuotient_le_natCard_state emptyOnlyDFA emptyOnlyDFA_accepts

end Cslib.Language.NerodeMinimalityTests
