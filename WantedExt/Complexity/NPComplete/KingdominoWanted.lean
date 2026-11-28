/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KINGDOMINO (K-TILING) is NP-complete

Source:
V.-H. Nguyen, K. Perrot and M. Vallet, "NP-completeness of the game Kingdomino",
Theoretical Computer Science 822 (2020), 23-35, doi:10.1016/j.tcs.2020.04.007
(arXiv:1909.02849), Section 3 (K-tiling problem) and Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KingdominoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kingdomino

/-!
# KINGDOMINO (K-TILING) is NP-complete

The one-player model of Kingdomino of Nguyen, Perrot and Vallet. A domino is a `2 × 1`
rectangle with a color and a number of crowns on each of its two cells. The board is `ℤ²`, with
a special cell, the tower, at `(0, 0)`. Given a sequence `τ` of dominoes, a K-tiling by `τ` is
built by placing the dominoes in the order of `τ`: a domino can be placed on a pair of adjacent
free positions if and only if at least one of its two cells is adjacent to an already placed
cell of the same color, or is adjacent to the tower; it is lost (not placed) if and only if it
can be placed nowhere. The score of a K-tiling is the sum, over its regions (the
monochromatic connected components of placed cells), of the number of cells of the region times
the number of crowns it contains.

INSTANCE: a sequence `τ` of dominoes and an integer `s`.
QUESTION: is there a K-tiling by `τ` with score at least `s`?

A placement of the `k`-th domino is `some (u, v)`, its first cell at `u` and its second at `v`
(all four rotations arise this way), or `none` when the domino is lost. Cells are adjacent when
they are adjacent in Mathlib's grid graph `hasse ℤ □ hasse ℤ` on `ℤ × ℤ`. The paper drops the
official bounding box (`5 × 5` or `7 × 7`) of the game, and so does this statement.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **KINGDOMINO (K-TILING) is NP-complete.** Source: Nguyen, Perrot and Vallet (2020),
Section 3 and Theorem 1. -/
public theorem_wanted kingdomino_npComplete :
    kingdominoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kingdominoDec

end MetaMathlibExt.Complexity.NPComplete.Kingdomino
