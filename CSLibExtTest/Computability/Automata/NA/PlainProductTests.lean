/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.NA.PlainProduct
public import CSLibExt.Computability.Languages.OmegaRegularClosure

/-!
# Tests for the plain product of Büchi automata

On Vardi's two automata, the plain product accepts nothing, while the pointer construction of
`exists_buchi_inf` yields an automaton accepting the only infinite word.
-/

@[expose] public section

namespace Cslib.PlainProductTests

open Automata Automata.NA Automata.ωAcceptor

/-- The only infinite word over `Unit`. -/
def unitWord : ωSequence Unit := ⟨fun _ => ()⟩

example : unitWord ∉ language (Buchi.plainProduct (Buchi.twoCycle {false})
    (Buchi.twoCycle {true})) := by
  rw [Buchi.language_plainProduct_twoCycle]
  exact id

example : ∃ (S : Type) (_ : Finite S) (a : Buchi S Unit), unitWord ∈ language a := by
  obtain ⟨S, hS, a, ha⟩ := Buchi.exists_buchi_inf (Buchi.twoCycle {false})
    (Buchi.twoCycle {true})
  refine ⟨S, hS, a, ?_⟩
  rw [ha, Buchi.language_twoCycle {false} ⟨false, rfl⟩,
    Buchi.language_twoCycle {true} ⟨true, rfl⟩, inf_top_eq]
  trivial

/-- With an empty accepting set the cyclic automaton accepts nothing, so the nonemptiness
hypothesis of `language_twoCycle` is needed. -/
example : unitWord ∉ language (Buchi.twoCycle ∅) := by
  rintro ⟨_, _, hacc⟩
  obtain ⟨_, h⟩ := hacc.exists
  exact h

end Cslib.PlainProductTests
