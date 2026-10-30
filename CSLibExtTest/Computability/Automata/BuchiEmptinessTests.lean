/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.NA.BuchiEmptiness
public import CSLibExt.Computability.Automata.NA.Parity
public import CSLibExt.Computability.Languages.ExampleInfinitelyOften

/-!
# Tests for Büchi emptiness and parity automata

* The emptiness test `isEmptyB` decides, by `decide`, that a two-state automaton without a cycle
  through its accepting state is empty and that the `infinitelyOften` automaton is nonempty;
  `isEmptyB_iff` turns the former into `language = ⊥`.
* A hand-built lasso gives an accepted ultimately periodic word.
* The parity presentation of a Büchi automaton accepts the same language.
-/

@[expose] public section

namespace Cslib.Automata.NA.Buchi.Tests

open Cslib.ωLanguage.Example ωAcceptor ωSequence

/-! ## An empty automaton -/

/-- Two states over a one-letter alphabet: the start state `0` moves to the accepting state `1`,
which has no outgoing transition, so no run exists at all. -/
def deadEnd : Buchi (Fin 2) Unit where
  Tr s _ t := s = 0 ∧ t = 1
  start := {0}
  accept := {1}

instance : ∀ s x t, Decidable (deadEnd.Tr s x t) := fun s _ t =>
  inferInstanceAs (Decidable (s = 0 ∧ t = 1))

instance : DecidablePred (· ∈ deadEnd.start) := fun s => inferInstanceAs (Decidable (s = 0))

instance : DecidablePred (· ∈ deadEnd.accept) := fun s => inferInstanceAs (Decidable (s = 1))

example : deadEnd.isEmptyB = true := by decide

example : language deadEnd = ⊥ := isEmptyB_iff.mp (by decide)

example : ¬ deadEnd.HasLasso := by decide

/-! ## A nonempty automaton -/

/-- The `infinitelyOften {true}` automaton over `Bool`. -/
abbrev recurTrue : Buchi Bool Bool := infinitelyOftenNa {true}

instance : ∀ s x t, Decidable (recurTrue.Tr s x t) := fun _ x t =>
  inferInstanceAs (Decidable (t = true ↔ x = true))

instance : DecidablePred (· ∈ recurTrue.start) := fun s => inferInstanceAs (Decidable (s = true))

instance : DecidablePred (· ∈ recurTrue.accept) := fun s => inferInstanceAs (Decidable (s = true))

example : recurTrue.isEmptyB = false := by decide

example : recurTrue.HasLasso := by decide

example : recurTrue.lassoStates = {true} := by decide

example : deadEnd.lassoStates = ∅ := by decide

/-- A hand-built lasso: from the start state `true`, read `false, true` back into the accepting
state `true`, then loop on `true`. -/
example : [false, true] ++ω (const [true]).flatten ∈ language recurTrue := by
  have h1 : recurTrue.Tr true false false := by
    change (false = true ↔ false ∈ ({true} : Set Bool))
    simp
  have h2 : recurTrue.Tr false true true := Iff.rfl
  have hloop : recurTrue.Tr true true true := Iff.rfl
  exact lasso_mem_language (s₀ := true) rfl rfl
    (LTS.MTr.stepL h1 (LTS.MTr.single _ h2)) (List.cons_ne_nil _ _) (LTS.MTr.single _ hloop)

/-- Nonemptiness yields an ultimately periodic accepted word. -/
example : ∃ u v : List Bool, v ≠ [] ∧ u ++ω (const v).flatten ∈ language recurTrue :=
  exists_lasso_word_of_nonempty (language_nonempty_iff_hasLasso.mpr (by decide))

/-! ## Büchi as parity -/

instance : DecidablePred (· ∈ (infinitelyOftenNa ({true} : Set Bool)).accept) := fun s =>
  inferInstanceAs (Decidable (s = true))

example : language (infinitelyOftenNa ({true} : Set Bool)).toParity = infinitelyOften {true} := by
  rw [language_toParity, language_infinitelyOftenNa]

example : (infinitelyOftenNa ({true} : Set Bool)).toParity.priority true = 2 := by decide

example : (infinitelyOftenNa ({true} : Set Bool)).toParity.priority false = 1 := by decide

end Cslib.Automata.NA.Buchi.Tests
