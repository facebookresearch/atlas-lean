/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FINITE STATE AUTOMATON INEQUIVALENCE for finite languages is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL1] FINITE STATE AUTOMATON
INEQUIVALENCE, p. 265, comment: the general problem is NP-complete "if `A₁` and `A₂` both
recognize finite languages (a property that can be checked in polynomial time)" (no separate
citation; the related [AL9] comment, p. 267, records that REGULAR EXPRESSION INEQUIVALENCE is
NP-complete for star-free expressions, which denote finite languages, citing L. J. Stockmeyer
and A. R. Meyer, "Word problems requiring exponential time (preliminary report)", STOC 1973,
1-9, doi:10.1145/800125.804029).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceFiniteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceFinite

open MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceUnary

/-!
# FINITE STATE AUTOMATON INEQUIVALENCE for finite languages is NP-complete

INSTANCE: two nondeterministic finite state automata `A₁` and `A₂` having the same input
alphabet `Σ` (an automaton `A = (Q, Σ, δ, q₀, F)` consists of a finite set `Q` of states, the
input alphabet `Σ`, a transition function `δ` mapping `Q × Σ` into subsets of `Q`, an initial
state `q₀`, and a set `F ⊆ Q` of accept states), where `A₁` and `A₂` both recognize finite
languages (the comment's restriction). QUESTION: do `A₁` and `A₂` recognize different
languages?

Automata are encoded as in `FiniteStateAutomatonInequivalenceUnaryWanted`
(`FiniteStateAutomatonInequivalenceUnary.AutomatonData`: the number `n` of states, the initial
state, the accept states and the transitions `((s, a), t)`), over the alphabet
`Σ = {0, …, m - 1}` of any size `m`. An automaton recognizes the language of the CSLibExt
`Cslib.Automata.EncodedNFA` it denotes
(`FiniteStateAutomatonInequivalenceUnary.toEncodedNFA`: start state `q₀`, no ε-moves), i.e.,
of the Mathlib `εNFA`. `WellFormed` requires both languages to be finite (`Set.Finite`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FINITE STATE AUTOMATON INEQUIVALENCE for automata recognizing finite languages is
NP-complete.** Source: Garey and Johnson (1979), [AL1], comment. -/
public theorem_wanted automatonInequivalenceFinite_npComplete :
    automatonInequivalenceFiniteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L automatonInequivalenceFiniteDec

end MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceFinite
