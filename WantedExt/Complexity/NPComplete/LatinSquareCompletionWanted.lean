/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LATIN SQUARE COMPLETION is NP-complete

Source:
C. J. Colbourn, "The complexity of completing partial Latin squares" (1984).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LatinSquareCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LatinSquareCompletion

/-!
# LATIN SQUARE COMPLETION is NP-complete

A partial Latin square: an `n` by `n` grid with entries `0` (blank) through `n`. The question
is whether it can be completed so that every row and column is a permutation of `1, …, n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LATIN SQUARE COMPLETION is NP-complete.** The decision problem LATIN SQUARE COMPLETION on
bitstrings lies in NP, and every decision problem in NP reduces to it by a polynomial-time
many-one reduction.

Source: C. J. Colbourn, "The complexity of
completing partial Latin squares" (1984). -/
public theorem_wanted latinSquareCompletion_npComplete :
    latinSquareCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L latinSquareCompletionDec

end MetaMathlibExt.Complexity.NPComplete.LatinSquareCompletion
