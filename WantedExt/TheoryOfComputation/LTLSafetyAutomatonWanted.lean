/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Safety automata for the general safety fragment (all states accepting)
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.LTL.VardiWolper

@[expose] public section

namespace Cslib.LTL.SafetyAutomatonWanted

open Cslib.Automata.ωAcceptor

/-!
# Safety automata for the general safety fragment

`Cslib.LTL.safety_general_buchi` gives every formula of the general safety
fragment `SafetyExt` a finite-state Büchi automaton with the same language,
via the full tableau construction. The stronger Kupferman-Vardi form asks for
a *safety* automaton: all states accepting, so the language is the set of
words with an infinite run. For `G ψ` one route is the powerset-of-copies
construction; the hard direction is König's lemma on the run tree. Source:
O. Kupferman and M. Y. Vardi, "Model checking of safety properties", Formal
Methods in System Design 19 (2001), 291-314.
-/

/-- **Safety automata for the general safety fragment.** Every general safety
formula has a safety automaton (all states accepting) with finitely many
states and the same ω-language. -/
public theorem_wanted safety_automaton_wanted :
    ∀ {Atom : Type*} (ψ : SafetyExt Atom),
      ∃ (S : Type) (_ : Finite S) (a : Cslib.Automata.NA.Buchi S (Set Atom)),
        Cslib.Automata.ωAcceptor.language a =
            Word.language (fun s a => a ∈ s) ψ.toLTL ∧ a.accept = Set.univ

end Cslib.LTL.SafetyAutomatonWanted
