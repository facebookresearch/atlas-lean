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


public import CSLibExt.Computability.Languages.Congruences.Universal

/-! # Tests for the universal property of DFA minimization -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.AutomataUniversalTests

/-- A two-state accessible DFA for the language containing only the empty word. -/
def emptyWordDFA : DFA Bool Bool where
  step _ _ := false
  start := true
  accept := {true}

theorem emptyWordDFA_accessible : Accessible emptyWordDFA := by
  intro q
  cases q with
  | false => exact ⟨[false], rfl⟩
  | true => exact ⟨[], rfl⟩

theorem emptyWordDFA_stateSeparated : StateSeparated emptyWordDFA := by
  intro p q hpq
  cases p <;> cases q
  · rfl
  · exfalso
    have h := Set.ext_iff.mp hpq []
    change (false ∈ ({true} : Set Bool) ↔ true ∈ ({true} : Set Bool)) at h
    simp at h
  · exfalso
    have h := Set.ext_iff.mp hpq []
    change (true ∈ ({true} : Set Bool) ↔ false ∈ ({true} : Set Bool)) at h
    simp at h
  · rfl

example : Function.Surjective (canonicalResidualHom emptyWordDFA emptyWordDFA_accessible) :=
  canonicalResidualHom_surjective emptyWordDFA emptyWordDFA_accessible

example : Function.Injective (canonicalResidualHom emptyWordDFA emptyWordDFA_accessible) :=
  (canonicalResidualHom_injective_iff emptyWordDFA emptyWordDFA_accessible).mpr
    emptyWordDFA_stateSeparated

noncomputable example : Bool ≃ Set.range emptyWordDFA.accepts.leftQuotient :=
  stateEquivResidualsOfSeparated emptyWordDFA emptyWordDFA_accessible
    emptyWordDFA_stateSeparated

example (x : List Bool) :
    canonicalResidualHom emptyWordDFA emptyWordDFA_accessible (emptyWordDFA.eval x) =
      emptyWordDFA.accepts.toDFA.eval x :=
  (canonicalResidualHom emptyWordDFA emptyWordDFA_accessible).map_eval x

example (f : DFAHom emptyWordDFA emptyWordDFA.accepts.toDFA) :
    f = canonicalResidualHom emptyWordDFA emptyWordDFA_accessible :=
  canonicalResidualHom_unique emptyWordDFA emptyWordDFA_accessible f

end Cslib.Language.AutomataUniversalTests
