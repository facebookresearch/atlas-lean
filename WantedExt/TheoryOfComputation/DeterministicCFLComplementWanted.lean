/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Languages.ContextFree.Deterministic

/-!
# Deterministic context-free languages are closed under complement

The statement is registered here as a `theorem_wanted`. The
definitions `Cslib.Automata.PDA.IsDeterministic` and
`Cslib.Language.IsDeterministicContextFree` are proved in `CSLibExt`.
The standard proof totalizes a deterministic pushdown automaton (adds
a dead state so every configuration has a move, and removes
`ε`-loops), switches it to acceptance by final state, complements
the accepting states, and converts back to end-marker acceptance
(on the end marker, drain exactly from accepting states). Totalization is the hard part: a pushdown
automaton can loop forever on `ε`-moves, and removing those loops
while preserving determinism and the accepted language is a large
construction, so closure under complement is left as a
`theorem_wanted`. Combined with the proved nonclosure of
context-free languages under complement
(`Cslib.Language.exists_isContextFree_compl_not_isContextFree`), it
would give another proof that the deterministic context-free
languages are a proper subset of the context-free languages.

The finite-alphabet hypothesis is essential: over an infinite
alphabet the statement is false. With `T = ℕ`, the empty language is
deterministic context-free (a machine that accepts nothing has finite
input support), but its complement contains every one-letter word,
hence every letter of the infinite alphabet, and no machine whose
transitions consume letters from a finite set can accept it.
-/

@[expose] public section

namespace Cslib.DeterministicCFLComplementWanted

open Cslib.Language

/-- The complement of a deterministic context-free language over a
finite alphabet is deterministic context-free.
Source: Ginsburg and Greibach, "Deterministic context free
languages", Information and Control 9 (1966), 620-648; Hopcroft,
Motwani, and Ullman, Introduction to Automata Theory, Languages, and
Computation, 3rd ed., Section 10.3. -/
public theorem_wanted isDeterministicContextFree_compl {T : Type*}
    [Finite T] {L : Language T} (hL : IsDeterministicContextFree L) :
    IsDeterministicContextFree Lᶜ

end Cslib.DeterministicCFLComplementWanted
