/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NONDANGO is NP-complete

Source:
S. Ruangwises, "Nondango is NP-complete", arXiv:2310.11447 (2023),
https://arxiv.org/abs/2310.11447.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NondangoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nondango

/-!
# NONDANGO is NP-complete

Nondango consists of a rectangular grid partitioned into polyominoes called regions, with some
cells containing a white circle. Some circles are colored black so that:
1. every region contains exactly one black circle;
2. there are no three consecutive circles (horizontally, vertically, or diagonally) having the
   same color.

INSTANCE: a rectangular grid partitioned into regions, some cells containing a circle.
QUESTION: can some circles be colored black so that rules 1 and 2 hold?

Three consecutive circles are circles in three consecutive cells of a row, a column, or a
diagonal (either direction); cells without circles have no color. A region is a polyomino: its
cells are connected through cells of the region sharing a side, as in Mathlib's grid graph
`pathGraph h □ pathGraph w` on `Fin h × Fin w`.

The instance is `(R, rows)`: the number `R` of regions, and the rows of the grid, top to bottom,
where the entry of a cell is `(region, circle)`, its region index and whether it contains a
circle. `WellFormed` requires at least one row and one column, rows of equal length, region
indices below `R`, and every region `k < R` connected (in particular nonempty).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NONDANGO is NP-complete.** Source: Ruangwises (2023), Theorem 1. -/
public theorem_wanted nondango_npComplete :
    nondangoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nondangoDec

end MetaMathlibExt.Complexity.NPComplete.Nondango
