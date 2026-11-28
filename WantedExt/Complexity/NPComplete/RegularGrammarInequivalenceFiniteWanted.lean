/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGULAR GRAMMAR INEQUIVALENCE for finite languages is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL14] REGULAR GRAMMAR INEQUIVALENCE,
p. 269, comment: the general problem is NP-complete "if both grammars generate finite languages
(a property that can be checked in polynomial time)" (no separate citation; the related [AL9]
comment, p. 267, records that REGULAR EXPRESSION INEQUIVALENCE is NP-complete for star-free
expressions, which denote finite languages, citing L. J. Stockmeyer and A. R. Meyer, "Word
problems requiring exponential time (preliminary report)", STOC 1973, 1-9,
doi:10.1145/800125.804029).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RegularGrammarInequivalenceFiniteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceFinite

open MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering
open MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceUnary

/-!
# REGULAR GRAMMAR INEQUIVALENCE for finite languages is NP-complete

INSTANCE: regular grammars `G₁ = (N₁, Σ, Π₁, S₁)` and `G₂ = (N₂, Σ, Π₂, S₂)`, where a regular
grammar is a context-free grammar in which each production has the form `A → aB` or `A → a`
with `A, B ∈ N` and `a ∈ Σ`, and both grammars generate finite languages (the comment's
restriction). QUESTION: do `G₁` and `G₂` generate different languages?

Grammars are encoded as in `ReynoldsCoveringWanted` (`ReynoldsCovering.GrammarData`: the number
of nonterminals, the initial nonterminal, and productions `(A, w)` whose right-hand-side symbols
are `(true, a)` for the terminal `a` and `(false, B)` for the nonterminal `B`), over the terminal
alphabet `Σ = {0, …, k - 1}` of any size `k`. A grammar generates the language of the
`Cslib.Language.EncodedCFG` it denotes (`ReynoldsCovering.toEncodedCFG`), i.e., of the Mathlib
`ContextFreeGrammar` with those productions. As in `RegularGrammarInequivalenceUnaryWanted`,
`WellFormed` requires every right-hand side to be `a B` or `a`
(`RegularGrammarInequivalenceUnary.IsRegularGrammar`); it also requires both languages to be
finite (`Set.Finite`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REGULAR GRAMMAR INEQUIVALENCE for grammars generating finite languages is
NP-complete.** Source: Garey and Johnson (1979), [AL14], comment. -/
public theorem_wanted regularGrammarInequivalenceFinite_npComplete :
    regularGrammarInequivalenceFiniteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L regularGrammarInequivalenceFiniteDec

end MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceFinite
