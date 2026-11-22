/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.DA.MathlibDFA

/-!
# Tests for the bridge between upstream deterministic automata and Mathlib DFAs

* Converting a Mathlib DFA (parity of `true`s) to an upstream `DA.FinAcc` and back is the
  identity, and the languages agree.
* The upstream canonical automaton of a language, renamed, is Mathlib's `Language.toDFA`, and
  for the language of a DFA it is the semantic minimal DFA.
-/

@[expose] public section

namespace Cslib.Automata.DA.FinAcc.Tests

/-- Number of `true`s modulo 2; accept an even count. -/
def parity : DFA Bool (Fin 2) := ⟨fun s b => if b then s + 1 else s, 0, {0}⟩

example : toDFA (ofDFA parity) = parity := rfl

example : Acceptor.language (ofDFA parity) = parity.accepts := accepts_ofDFA parity

example (w : List Bool) : w ∈ Acceptor.language (ofDFA parity) ↔ parity.eval w = 0 := by
  rw [accepts_ofDFA, DFA.mem_accepts]
  exact Set.mem_singleton_iff

example : DFA.reindex (nerodeQuotientEquivResidual parity.accepts)
    (toDFA parity.accepts.NerodeCongruenceDA) = parity.accepts.toDFA :=
  reindex_nerodeCongruenceDA _

example : DFA.reindex ((nerodeQuotientEquivResidual parity.accepts).trans
    (Cslib.Language.leftQuotientEquivReachableResiduals parity))
    (toDFA parity.accepts.NerodeCongruenceDA) = Cslib.Language.minimizedDFA parity :=
  reindex_nerodeCongruenceDA_eq_minimizedDFA parity

end Cslib.Automata.DA.FinAcc.Tests
