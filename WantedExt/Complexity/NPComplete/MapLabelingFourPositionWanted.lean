/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAP LABELING WITH FOUR POSITIONS is NP-complete

Source:
M. Formann and F. Wagner, "A packing problem with applications to lettering of maps", in
*Proceedings of the 7th Annual Symposium on Computational Geometry (SoCG 1991)*, ACM (1991),
281-288, doi:10.1145/109648.109680.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MapLabelingFourPositionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MapLabelingFourPosition

/-!
# MAP LABELING WITH FOUR POSITIONS is NP-complete

INSTANCE: a finite set of points in the plane with integer coordinates and a positive rational
`σ`.
QUESTION: can each point be labeled by an axis-parallel `σ × σ` square that has the point as one
of its four corners, such that no two labels overlap (their interiors are disjoint; labels may
touch)?

The points are a duplicate-free list of integer pairs, each integer given as a pair
`(positive part, negative part)` of natural numbers as in `ZeroOneILPWanted`; `σ = p / q` with
`p, q > 0`. A labeling chooses for each point `(x, y)` a corner `(a, b) ∈ {0, 1}²`, and its label
is the square with lower-left corner `(x - aσ, y - bσ)`. Two open `σ × σ` squares with lower-left
corners `(u, v)` and `(u', v')` intersect iff `|u - u'| < σ` and `|v - v'| < σ`; multiplying by
`q`, the labels of points `j ≠ k` are disjoint iff `|q(xⱼ - xₖ) - p(aⱼ - aₖ)| ≥ p` or
`|q(yⱼ - yₖ) - p(bⱼ - bₖ)| ≥ p` (`AtLeast`). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAP LABELING WITH FOUR POSITIONS is NP-complete.** Source: Formann and Wagner (1991). -/
public theorem_wanted mapLabelingFourPosition_npComplete :
    mapLabelingFourPositionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mapLabelingFourPositionDec

end MetaMathlibExt.Complexity.NPComplete.MapLabelingFourPosition
