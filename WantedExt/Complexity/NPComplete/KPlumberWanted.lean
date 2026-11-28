/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KPLUMBER is NP-complete

Source:
D. Král', V. Majerech, J. Sgall, T. Tichý and G. Woeginger, "It is tough to be a plumber",
Theoretical Computer Science 313 (2004), 473-484, doi:10.1016/j.tcs.2002.12.002.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KPlumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KPlumber

/-!
# KPLUMBER is NP-complete

KPlumber is played on a rectangular grid of cells, each holding a rotatable square tile that
depicts some segments of a pipe: each of the four edges of a tile is either empty or carries an
unterminated pipe end. The tile types are the empty tile, the dead end, the straight line, the
curve, the T-join and the X-join, in all their rotations; together these are all `2⁴` patterns
of pipe ends on the four sides.

INSTANCE: an `m × n` grid of tiles, `m, n ≥ 1`.
QUESTION: can the tiles be rotated so that all unterminated pipe ends are paired along interior
edges, that is, every pipe end of a tile meets a pipe end of the neighbouring tile across the
same edge, and no pipe end lies on the boundary of the grid?

A tile is the quadruple `(north, east, south, west)` of booleans saying which of its sides carry
a pipe end; the sides are numbered `0` (north), `1` (east), `2` (south), `3` (west). The grid
lists the tiles row by row: the tile of row `r < m` and column `c < n` is entry `r * n + c`.
Rotating a tile clockwise by `k` quarter turns moves the pipe end of side `s` to side `s + k`
(mod `4`). Row `0` is the top row and column `0` the left column.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **KPLUMBER is NP-complete.** Source: Král', Majerech, Sgall, Tichý and Woeginger (2004). -/
public theorem_wanted kPlumber_npComplete :
    kPlumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kPlumberDec

end MetaMathlibExt.Complexity.NPComplete.KPlumber
