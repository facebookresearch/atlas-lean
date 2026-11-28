/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BATTLESHIPS is NP-complete

Source:
M. Sevenster, "Battleships as decision problem", ICGA Journal 27 (2004), 142-149,
doi:10.3233/ICG-2004-27303.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BattleshipsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Battleships

/-!
# BATTLESHIPS is NP-complete

Sevenster (2004) treats an `m × n` Battleships puzzle as a tuple `⟨I, C, R, F⟩`: the initial
filling `I` of the grid, which marks each cell as `ship`, `water` or `?`; the column tally `C`
and the row tally `R`, which give a number for every column and every row; and the fleet `F`,
with "`F(k)` ships of ship-length `k`" (every ship has width `1`). A solution places the ships
so that

* C1: all ships in the fleet are put in the grid;
* C2: the indications in the initial grid are respected;
* C3: no two ships occupy adjacent (orthogonally or diagonally) squares;
* C4: the number of ship segments in column (row) `i` is equal to the `i`th value of the
  column (row) tally.

BATTLESHIPS asks: given a Battleships puzzle, does it have a solution?

Here the grid has `m = R.length` rows and `n = C.length` columns (rows and columns are numbered
from `0`). The fleet is the list `F` with `F[k] = F(k + 1)`, the number of ships of length
`k + 1`; lengths beyond the list have no ships. The cells of `I` other than `?` are listed as
`((row, column), b)`, with `b = true` for a ship segment and `b = false` for water. A ship is
placed by its first cell, an orientation (`true` for vertical, extending down; `false` for
horizontal, extending right) and its length; the ship segments of the solution are the cells
covered by the placed ships. C3 says that cells of two different placed ships differ by at least
two in some coordinate; in particular different ships share no cell.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BATTLESHIPS is NP-complete.** Source: Sevenster (2004). -/
public theorem_wanted battleships_npComplete :
    battleshipsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L battleshipsDec

end MetaMathlibExt.Complexity.NPComplete.Battleships
