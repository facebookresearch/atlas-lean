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
# Deterministic context-free languages are a proper subset of the context-free languages

The statement is registered here as a `theorem_wanted`. The
definitions `Cslib.Automata.PDA.IsDeterministic` and
`Cslib.Language.IsDeterministicContextFree`, and the inclusion
`Cslib.Language.IsDeterministicContextFree.isContextFree`, are proved
in `CSLibExt`. The separation needs a genuinely non-deterministic
argument: a witness such as the even-length palindromes
`{w w^R}` over a two-letter alphabet is context-free but admits no
deterministic pushdown automaton, because a deterministic machine
cannot guess the middle of the word, and the end marker does not
help since it arrives only after the middle has passed. Formalizing that impossibility
argument (via the deterministic-pumping / prefix argument) is a large
argument, so the separation is left as a `theorem_wanted`. Together
with the proved inclusion it says the deterministic context-free
languages are a proper subset of the context-free languages.
-/

@[expose] public section

namespace Cslib.DeterministicCFLSeparationWanted

open Cslib.Language

/-- Some context-free language is not deterministic context-free.
Source: Ginsburg and Greibach, "Deterministic context free
languages", Information and Control 9 (1966), 620-648; Hopcroft,
Motwani, and Ullman, Introduction to Automata Theory, Languages, and
Computation, 3rd ed., Section 10.3. -/
public theorem_wanted exists_isContextFree_not_isDeterministicContextFree :
    ∃ (L : Language (Fin 2)),
      L.IsContextFree ∧ ¬ IsDeterministicContextFree L

end Cslib.DeterministicCFLSeparationWanted
