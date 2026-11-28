/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SQUARE-TILING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GP13] SQUARE-TILING
(credited there to unpublished 1977 work of Garey, Johnson, and Papadimitriou);
E. D. Demaine and M. L. Demaine, "Jigsaw puzzles, edge matching, and polyomino
packing: connections and complexity", Graphs and Combinatorics 23 (2007),
suppl. 1, 195-208, doi:10.1007/s00373-007-0713-4 (records the attribution).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SquareTilingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SquareTiling

/-!
# SQUARE-TILING is NP-complete

INSTANCE: a set `C` of colors, a collection `T ⊆ C⁴` of tiles (a tile `⟨a, b, c, d⟩` has top
color `a`, right color `b`, bottom color `c`, left color `d`), and a positive integer
`N ≤ |C|`. QUESTION: is there a tiling of an `N × N` square using the tiles in `T`, that is,
an assignment of a tile `f(i, j) ∈ T` to each ordered pair `(i, j)`, `1 ≤ i, j ≤ N`, such that
(1) if `f(i, j) = ⟨a, b, c, d⟩` and `f(i + 1, j) = ⟨a', b', c', d'⟩` then `b = d'`, and
(2) if `f(i, j) = ⟨a, b, c, d⟩` and `f(i, j + 1) = ⟨a', b', c', d'⟩` then `c = a'`?

So `i` counts columns left to right and `j` counts rows top to bottom; tiles are not rotated,
and a tile may be used any number of times. Positions are indexed from `0` here. The color set
`C` is listed explicitly, so `N ≤ |C|` bounds the side length by the input length.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SQUARE-TILING is NP-complete.** Source: Garey and Johnson (1979), [GP13]; Demaine and
Demaine (2007). -/
public theorem_wanted squareTiling_npComplete :
    squareTilingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L squareTilingDec

end MetaMathlibExt.Complexity.NPComplete.SquareTiling
