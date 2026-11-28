/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FINITE STATE AUTOMATON INEQUIVALENCE over a one-letter alphabet is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL1] FINITE STATE AUTOMATON
INEQUIVALENCE, p. 265, comment: the general problem is NP-complete if `|Σ| = 1` (no separate
citation; the related [AL9] comment records that REGULAR EXPRESSION INEQUIVALENCE is
NP-complete if `|Σ| = 1`, citing L. J. Stockmeyer and A. R. Meyer, "Word problems requiring
exponential time (preliminary report)", STOC 1973, 1-9, doi:10.1145/800125.804029).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceUnaryDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceUnary

/-!
# FINITE STATE AUTOMATON INEQUIVALENCE over a one-letter alphabet is NP-complete

INSTANCE: two nondeterministic finite state automata `A₁` and `A₂` having the same input
alphabet `Σ`, where `|Σ| = 1` (an automaton `A = (Q, Σ, δ, q₀, F)` consists of a finite set `Q`
of states, the input alphabet `Σ`, a transition function `δ` mapping `Q × Σ` into subsets of
`Q`, an initial state `q₀`, and a set `F ⊆ Q` of accept states). QUESTION: do `A₁` and `A₂`
recognize different languages?

The alphabet is `Σ = {0, …, m - 1}` with `m = 1` (`WellFormed`), as in
`RegularExpressionInequivalenceUnaryWanted`. An automaton is given by its number `n` of states
(`Q = {0, …, n - 1}`), its initial state, its list of accept states and its list of transitions
`((s, a), t)` ("on letter `a`, state `s` may move to `t`"), so `δ(s, a)` is the set of the `t`
listed with `(s, a)`. It is read as a CSLibExt `Cslib.Automata.EncodedNFA` with the single start
state `q₀` and no ε-moves, and recognizes `EncodedNFA.language`, the language of the Mathlib
`εNFA` it denotes.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FINITE STATE AUTOMATON INEQUIVALENCE over a one-letter alphabet is NP-complete.** Source:
Garey and Johnson (1979), [AL1], comment. -/
public theorem_wanted automatonInequivalenceUnary_npComplete :
    automatonInequivalenceUnaryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L automatonInequivalenceUnaryDec

end MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceUnary
