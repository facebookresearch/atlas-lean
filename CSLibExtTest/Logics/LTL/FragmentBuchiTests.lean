/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for Büchi automata for the LTL safety fragment
-/
module

public import CSLibExt.Logics.LTL.FragmentBuchi

/-!
# Tests for Büchi automata for the LTL safety fragment

The `G F p` automaton for the atom `p` accepts the language of `G F p`, and
every safety formula has a Büchi automaton with the same language, by
`exists_buchi_of_safety`.
-/

@[expose] public section

namespace Cslib.LTL.FragmentBuchi.Tests

open Cslib.ωLanguage.Example
open Cslib.Automata.ωAcceptor

/-- The `G F p` automaton for the atom `p` accepts the language of `G F p`. -/
example : language (infinitelyOftenNa {s : Set Unit | () ∈ s}) =
    Word.language (fun s a => a ∈ s)
      (Formula.always (Formula.eventually (.atom ()))) :=
  language_always_eventually (PropFormula.atom ())

/-- The `F G p` automaton for the atom `p` accepts the language of `F G p`. -/
example : language (eventuallyAlwaysNa {s : Set Unit | () ∈ s}) =
    Word.language (fun s a => a ∈ s)
      (Formula.eventually (Formula.always (.atom ()))) :=
  language_eventually_always (PropFormula.atom ())

/-- The safety formula `G p ∧ X G p` has a finite-state Büchi automaton with the same language. -/
example : ∃ (S : Type) (_ : Finite S) (a : Cslib.Automata.NA.Buchi S (Set Unit)),
    language a = Word.language (fun s a => a ∈ s)
      (Safety.toLTL (.and (.alwaysProp (.atom ()))
        (.next (.alwaysProp (.atom ()))))) :=
  exists_buchi_of_safety _

end Cslib.LTL.FragmentBuchi.Tests
