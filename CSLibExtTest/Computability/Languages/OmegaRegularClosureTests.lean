/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.OmegaRegularClosure
public import CSLibExt.Computability.Languages.ExampleInfinitelyOften

/-!
# Tests for the Boolean closure of Büchi automata

The closure theorems are applied to the two-state automaton for "infinitely many letters in
`p`", and complementation is also applied over the empty alphabet, which the upstream
complementation theorem excludes.
-/

@[expose] public section

namespace Cslib.OmegaRegularClosureTests

open Automata Automata.NA Automata.ωAcceptor ωLanguage.Example

/-- The complement of "infinitely many `true`" is recognized, and contains `false^ω`. -/
example : ∃ (S : Type) (_ : Finite S) (a : Buchi S Bool),
    language a = (infinitelyOften {true})ᶜ ∧ ωSequence.const false ∈ language a := by
  obtain ⟨S, hS, a, ha⟩ := Buchi.exists_buchi_compl (infinitelyOftenNa ({true} : Set Bool))
  rw [language_infinitelyOftenNa] at ha
  refine ⟨S, hS, a, ha, ?_⟩
  rw [ha, compl_infinitelyOften]
  exact Filter.Eventually.of_forall fun _ => by simp

/-- Intersection: infinitely many `true` and infinitely many `false`. -/
example : ∃ (S : Type) (_ : Finite S) (a : Buchi S Bool),
    language a = infinitelyOften {true} ⊓ infinitelyOften {false} := by
  obtain ⟨S, hS, a, ha⟩ := Buchi.exists_buchi_inf (infinitelyOftenNa ({true} : Set Bool))
    (infinitelyOftenNa ({false} : Set Bool))
  exact ⟨S, hS, a, by rw [ha, language_infinitelyOftenNa, language_infinitelyOftenNa]⟩

/-- Union: infinitely many `true` or infinitely many `false` (that is, every word). -/
example : ∃ (S : Type) (_ : Finite S) (a : Buchi S Bool),
    language a = infinitelyOften {true} ⊔ infinitelyOften {false} := by
  obtain ⟨S, hS, a, ha⟩ := Buchi.exists_buchi_sup (infinitelyOftenNa ({true} : Set Bool))
    (infinitelyOftenNa ({false} : Set Bool))
  exact ⟨S, hS, a, by rw [ha, language_infinitelyOftenNa, language_infinitelyOftenNa]⟩

/-- Complementation over the empty alphabet, where `Inhabited` fails. -/
example (a : Buchi Unit Empty) :
    ∃ (S : Type) (_ : Finite S) (a' : Buchi S Empty), language a' = (language a)ᶜ :=
  Buchi.exists_buchi_compl a

example : ¬ Nonempty (Inhabited Empty) := fun ⟨⟨e⟩⟩ => e.elim

end Cslib.OmegaRegularClosureTests
