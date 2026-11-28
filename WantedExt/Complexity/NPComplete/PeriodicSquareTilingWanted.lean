/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERIODIC SQUARE-TILING WITH BOUNDED PERIOD is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GP13] SQUARE-TILING, comment
(p. 257: "Variant in which we ask if T can be used to tile the entire plane (Z×Z)
'periodically' with period less than N is also NP-complete"), credited there to
[Garey, Johnson, and Papadimitriou, 1977], listed in the book's bibliography as unpublished
results.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PeriodicSquareTilingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PeriodicSquareTiling

open MetaMathlibExt.Complexity.NPComplete.SquareTiling (SquareTilingInstance)

/-!
# PERIODIC SQUARE-TILING WITH BOUNDED PERIOD is NP-complete

INSTANCE: a set `C` of colors, a collection `T ⊆ C⁴` of tiles (a tile `⟨a, b, c, d⟩` has top
color `a`, right color `b`, bottom color `c`, left color `d`), and a positive integer
`N ≤ |C|`. QUESTION: can `T` be used to tile the entire plane `ℤ × ℤ` periodically with period
less than `N`?

This is the variant recorded in the comment of Garey and Johnson's [GP13] SQUARE-TILING
(`SquareTilingWanted`). The instance type and `SquareTiling.WellFormed` (distinct colors,
distinct tiles, tile colors in `C`, `0 < N ≤ |C|`) are the parent's, unchanged. A tiling of the
plane assigns a tile `f(x, y) ∈ T` to every `(x, y) ∈ ℤ × ℤ` (`x` counts columns left to
right, `y` rows top to bottom, as in the parent) with the parent's two matching rules at every
position: the right color of `f(x, y)` is the left color of `f(x + 1, y)`, and the bottom color
of `f(x, y)` is the top color of `f(x, y + 1)`. Tiles are not rotated and may be reused.

Period: the tiling is periodic with period `p` when it is invariant under the translations by
`p` in both directions, `f(x + p, y) = f(x, y) = f(x, y + p)`; the question asks for such a
tiling with `0 < p < N`. Such a tiling is the same thing as a `p × p` tiling whose opposite
borders also match (a tiling of the torus), so a certificate has `p² < N² ≤ |C|²` tiles.
The source does not define "period" further; this statement reads it as one period `p`
shared by both coordinate directions. The bound `N ≤ |C|` is the parent's instance condition;
padding `C` with unused colors meets it for any `N` given in unary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PERIODIC SQUARE-TILING WITH BOUNDED PERIOD is NP-complete.** Source: Garey and Johnson
(1979), [GP13], comment (Garey, Johnson, and Papadimitriou, unpublished). -/
public theorem_wanted periodicSquareTiling_npComplete :
    periodicSquareTilingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L periodicSquareTilingDec

end MetaMathlibExt.Complexity.NPComplete.PeriodicSquareTiling
