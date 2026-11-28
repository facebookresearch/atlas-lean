/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PACKING SQUARES INTO A SQUARE is NP-complete

Source:
J. Y.-T. Leung, T. W. Tam, C. S. Wong, G. H. Young and F. Y. L. Chin, "Packing squares into a
square", Journal of Parallel and Distributed Computing 10 (1990), 271-275,
doi:10.1016/0743-7315(90)90019-L.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PackingSquaresIntoSquareDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PackingSquaresIntoSquare

open StripPacking (StripPackingFeasible)

/-!
# PACKING SQUARES INTO A SQUARE is NP-complete

INSTANCE: positive integer side lengths `s₁, ..., sₙ` and a positive integer `s`. QUESTION: can
the `n` squares of sides `s₁, ..., sₙ` be packed into the square of side `s`, axis-parallel and
without overlap (interiors pairwise disjoint)?

This is the special case of STRIP PACKING (`StripPackingWanted`) in which every rectangle is a
square `sⱼ × sⱼ` and the strip has width `s` and height bound `s`; the question is that module's
`StripPackingFeasible` on the instance `([(s₁, s₁), ..., (sₙ, sₙ)], s, s)`: the squares are
placed, without rotation (a square is unchanged by it), at integer positions inside the
`s × s` square, and any two are separated horizontally or vertically. Integer positions lose
nothing: pushing every square of a packing down and then to the left as far as possible makes
each coordinate of a lower-left corner a sum of side lengths.

Leung, Tam, Wong, Young and Chin prove that deciding whether a set of squares can be packed into
a larger square is strongly NP-complete, answering a question of Li and Cheng. Membership in NP:
the positions are a certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PACKING SQUARES INTO A SQUARE is NP-complete.** Source: Leung, Tam, Wong, Young and Chin
(1990). -/
public theorem_wanted packingSquaresIntoSquare_npComplete :
    packingSquaresIntoSquareDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L packingSquaresIntoSquareDec

end MetaMathlibExt.Complexity.NPComplete.PackingSquaresIntoSquare
