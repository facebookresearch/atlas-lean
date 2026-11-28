/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORT SYNCHRONIZING WORD is NP-complete

Source:
D. Eppstein, "Reset sequences for monotonic automata", SIAM Journal on Computing 19(3) (1990),
500-510, doi:10.1137/0219033, Theorem 8 (given an automaton and an integer `m`, deciding
whether the automaton has a reset sequence of length at most `m` is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShortSynchronizingWordDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortSynchronizingWord

/-!
# SHORT SYNCHRONIZING WORD is NP-complete

INSTANCE: a deterministic finite automaton `(S, Σ, δ)` and an integer `m`.
QUESTION: does the automaton have a reset sequence of length at most `m`, that is, a word `τ`
with `|τ| ≤ m` and `|δ(τ, S)| = 1`, so that `τ` leaves the automaton in one particular state no
matter which state it started at?

The states are `Fin n` and the letters are `Fin k`. The automaton is given by its transition
table: row `q` lists `δ(q, a)` for `a = 0, …, k - 1`. Start and accepting states play no role in
the question, so the instance has none, and the automaton is a CSLib functional labelled
transition system `Cslib.FLTS (Fin n) (Fin k)` (a deterministic transition function). Its
extended transition function `Cslib.FLTS.mtr` reads a word from left to right, as the source's
`δ(τ, s)` does (`δ(τ₁τ₂, s) = δ(τ₂, δ(τ₁, s))`). The bound `m` uses the canonical binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHORT SYNCHRONIZING WORD is NP-complete.** Source: Eppstein (1990), Theorem 8. -/
public theorem_wanted shortSynchronizingWord_npComplete :
    shortSynchronizingWordDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortSynchronizingWordDec

end MetaMathlibExt.Complexity.NPComplete.ShortSynchronizingWord
