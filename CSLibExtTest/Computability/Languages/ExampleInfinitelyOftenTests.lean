/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ExampleInfinitelyOften

/-!
# Tests for the "infinitely often" and "eventually always" Büchi automata

* The constant word `true^ω` is in `infinitelyOften {true}`, and the word `false^ω` is not.
* `infinitelyOften` and `eventuallyAlways` are dual under complement.
* Using upstream closure (`Cslib.ωLanguage.IsRegular.inf`, `IsRegular.compl`): words with
  infinitely many `a`s and infinitely many `b`s form an ω-regular language, and so does the
  complement of `eventuallyAlways`.
-/

@[expose] public section

namespace Cslib.ωLanguage.Example.Tests

open Filter ωSequence Automata ωAcceptor

example : const true ∈ language (infinitelyOftenNa ({true} : Set Bool)) := by
  rw [language_infinitelyOftenNa, mem_infinitelyOften]
  exact Frequently.of_forall fun _ => rfl

example : const false ∉ language (infinitelyOftenNa ({true} : Set Bool)) := by
  rw [language_infinitelyOftenNa, mem_infinitelyOften]
  intro h
  obtain ⟨k, hk⟩ := h.exists
  exact absurd hk (by simp [get_const])

example : const false ∈ language (eventuallyAlwaysNa ({false} : Set Bool)) := by
  rw [language_eventuallyAlwaysNa, mem_eventuallyAlways]
  exact Eventually.of_forall fun _ => rfl

example (p : Set (Fin 3)) : (eventuallyAlways p)ᶜ = infinitelyOften pᶜ := by
  rw [← compl_compl (infinitelyOften pᶜ), compl_infinitelyOften, compl_compl]

/-- Infinitely many `0`s and infinitely many `1`s, through upstream intersection closure. -/
example : (infinitelyOften ({0} : Set (Fin 3)) ⊓ infinitelyOften {1}).IsRegular :=
  (isRegular_infinitelyOften _).inf (isRegular_infinitelyOften _)

/-- The complement of a persistence language, through upstream complementation. -/
example : (eventuallyAlways ({0} : Set (Fin 3)))ᶜ.IsRegular :=
  (isRegular_eventuallyAlways _).compl

end Cslib.ωLanguage.Example.Tests
