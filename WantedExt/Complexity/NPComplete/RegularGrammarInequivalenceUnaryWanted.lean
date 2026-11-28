/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGULAR GRAMMAR INEQUIVALENCE over a one-letter alphabet is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL14] REGULAR GRAMMAR INEQUIVALENCE,
p. 269, comment: the general problem is NP-complete if `|Σ| = 1` (no separate
citation; the related [AL9] comment records that REGULAR EXPRESSION INEQUIVALENCE is
NP-complete if `|Σ| = 1`, citing L. J. Stockmeyer and A. R. Meyer, "Word problems requiring
exponential time (preliminary report)", STOC 1973, 1-9, doi:10.1145/800125.804029).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RegularGrammarInequivalenceUnaryDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceUnary

open MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering

/-!
# REGULAR GRAMMAR INEQUIVALENCE over a one-letter alphabet is NP-complete

INSTANCE: regular grammars `G₁ = (N₁, Σ, Π₁, S₁)` and `G₂ = (N₂, Σ, Π₂, S₂)`, where a regular
grammar is a context-free grammar in which each production has the form `A → aB` or `A → a`
with `A, B ∈ N` and `a ∈ Σ`, and `|Σ| = 1` (the comment's restriction). QUESTION: do `G₁` and
`G₂` generate different languages?

Grammars are encoded as in `ReynoldsCoveringWanted` (`ReynoldsCovering.GrammarData`: the number
of nonterminals, the initial nonterminal, and productions `(A, w)` whose right-hand-side symbols
are `(true, a)` for the terminal `a` and `(false, B)` for the nonterminal `B`), over the terminal
alphabet `Σ = {0, …, k - 1}` with `k = 1`. A grammar generates the language of the
`Cslib.Language.EncodedCFG` it denotes (`ReynoldsCovering.toEncodedCFG`), i.e., of the Mathlib
`ContextFreeGrammar` with those productions. `WellFormed` requires every right-hand side to be
`a B` or `a` (`isRegularRhs`), Garey and Johnson's form.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REGULAR GRAMMAR INEQUIVALENCE over a one-letter alphabet is NP-complete.** Source: Garey
and Johnson (1979), [AL14], comment. -/
public theorem_wanted regularGrammarInequivalenceUnary_npComplete :
    regularGrammarInequivalenceUnaryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L regularGrammarInequivalenceUnaryDec

end MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceUnary
