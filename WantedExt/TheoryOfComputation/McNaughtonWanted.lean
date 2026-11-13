/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# McNaughton's theorem: deterministic Muller automata recognize all ω-regular languages
-/
module

public import Batteries.Util.ProofWanted
public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.NA.Basic

@[expose] public section

namespace Cslib.McNaughtonWanted

open Cslib.Automata.NA
open Cslib.Automata.DA
open Cslib.Automata.ωAcceptor

/-!
# McNaughton's theorem

Every ω-regular language, recognized by a nondeterministic Büchi automaton, is
recognized by a deterministic Muller automaton. This is the hard direction of
upstream `Cslib.ωLanguage.IsRegular.iff_da_muller` (currently a
`proof_wanted`); the converse direction is immediate, since a deterministic
Muller automaton is a nondeterministic Muller automaton and Muller automata
recognize ω-regular languages.
-/

/-- Source: R. McNaughton, "Testing and generating infinite sequences by a
finite automaton", *Information and Control* 9 (1966), 521-530. -/
public theorem_wanted mcNaughton_wanted :
    ∀ (n k : ℕ) (a : Cslib.Automata.NA.Buchi (Fin n) (Fin k)),
      ∃ (m : ℕ) (d : Cslib.Automata.DA.Muller (Fin m) (Fin k)),
        language d = language a

end Cslib.McNaughtonWanted
