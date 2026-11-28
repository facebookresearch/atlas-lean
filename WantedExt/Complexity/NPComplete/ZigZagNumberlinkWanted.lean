/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZIG-ZAG NUMBERLINK is NP-complete

Source:
A. Adcock, E. D. Demaine, M. L. Demaine, M. P. O'Brien, F. Reidl, F. Sánchez Villaamil, and
B. D. Sullivan, "Zig-zag Numberlink is NP-complete", Journal of Information Processing 23(3)
(2015), 239-245, doi:10.2197/ipsjjip.23.239 (arXiv:1410.5845, Definitions 1-4 and Theorem 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ZigZagNumberlinkDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ZigZagNumberlink

/-!
# ZIG-ZAG NUMBERLINK is NP-complete

INSTANCE: an `m × n` board of squares and a set of terminal pairs, each a pair of distinct
squares, with all terminals distinct.
QUESTION: is there a set of paths, one for each terminal pair, each connecting its pair, such
that each square of the board is contained in exactly one path?

Paths are sequences of distinct squares, consecutive squares adjacent (sharing a side), and
together they must cover the whole board. "Zig-zag" names the absence of a bend restriction: the
source contrasts it with Classic Numberlink, whose paths may not have unnecessary bends, and says
the zig-zag version "allows links to zig-zag arbitrarily to fill the grid". Paths are not
required to turn at every square.

The board is given explicitly, row by row: a list of `m` rows of `n` squares, a square holding
`0` (no terminal) or `c ≥ 1` (a terminal of pair `c`), so the input size is at least the number
of squares. Squares are `Fin m × Fin n`, adjacent in Mathlib's grid graph
`pathGraph m □ pathGraph n` (`Grid`); a path is a Mathlib walk with `Walk.IsPath`. A solution
assigns every square the pair whose path contains it (`owner`); for each pair `c` with terminals
`s ≠ t`, some path from `s` to `t` contains exactly the squares owned by `c`. Every square is
owned by some pair, so the paths cover the board, and squares owned by different pairs are on
different paths, so each square is on exactly one path.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ZIG-ZAG NUMBERLINK is NP-complete.** Source: Adcock, Demaine, Demaine, O'Brien, Reidl,
Sánchez Villaamil, and Sullivan (2015), Theorem 1. -/
public theorem_wanted zigZagNumberlink_npComplete :
    zigZagNumberlinkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zigZagNumberlinkDec

end MetaMathlibExt.Complexity.NPComplete.ZigZagNumberlink
