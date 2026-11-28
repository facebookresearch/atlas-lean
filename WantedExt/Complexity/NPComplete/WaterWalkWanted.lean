/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WATER WALK is NP-complete

Source:
P. Eua-anant, P. Apinyanon, T. Jirachaisri, N. Ruangsuksriwong and S. Ruangwises,
"NP-completeness proofs of All or Nothing, Water Walk, and Remembered Length using the
T-metacell framework", arXiv:2510.21938 (2025), Section 2.2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WaterWalkDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WaterWalk

/-!
# WATER WALK is NP-complete

Eua-anant, Apinyanon, Jirachaisri, Ruangsuksriwong and Ruangwises (2025), Section 2.2: "Water
Walk is a pencil puzzle invented by Martin Ender. In this puzzle, a rectangular grid consisting
of ground (white) and water (blue) cells is given, with some ground cells containing a number.
The goal is to draw a non-crossing loop passing through orthogonally adjacent cells to satisfy
the following three constraints.
1. The loop must pass through all numbered cells.
2. For each numbered cell, the number of continuous ground cells in the loop in the section
   where it passes through that cell must be exactly equal to the number written on it.
3. The loop cannot pass through three consecutive water cells."

INSTANCE: a rectangular grid of ground and water cells, some ground cells numbered.
QUESTION: is there a loop satisfying rules 1-3?

Representation. The grid is given row by row: entry `c` of row `r` is `(water, number)` for cell
`(r, c)`, with number `0` for an unnumbered cell. Cells are `Fin m × Fin n`, adjacent when they
share a side in Mathlib's grid graph `pathGraph m □ pathGraph n`. The loop is a cycle `c` of the
grid graph (`SimpleGraph.Walk.IsCycle`). Write `L` for its length and `c_j` for its `j`-th cell,
indices taken mod `L`. Rule 3: no three cyclically consecutive cells `c_j, c_{j+1}, c_{j+2}` are
all water. Rule 2: if `c_j` carries number `k`, then either every cell of the loop is ground and
`k = L` (the section is the whole loop), or the section of the loop through `c_j` is a run of
exactly `k` ground cells `c_{j-a}, …, c_{j-a+k-1}` (with `0 ≤ a < k`) between two water cells
`c_{j-a-1}` and `c_{j-a+k}`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WATER WALK is NP-complete.** Source: Eua-anant, Apinyanon, Jirachaisri, Ruangsuksriwong
and Ruangwises (2025). -/
public theorem_wanted waterWalk_npComplete :
    waterWalkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L waterWalkDec

end MetaMathlibExt.Complexity.NPComplete.WaterWalk
