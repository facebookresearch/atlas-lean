/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TILEPAINT is NP-complete

Source:
C. Iwamoto and T. Ide, "Five Cells and Tilepaint are NP-complete", IEICE Transactions on
Information and Systems E105-D(3) (2022), 508-516, doi:10.1587/transinf.2021FCP0001,
Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TilepaintDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Tilepaint

/-!
# TILEPAINT is NP-complete

INSTANCE: a rectangular grid of cells divided into tiles, the areas enclosed by bold lines, and
a number assigned to each row and each column.
QUESTION: can cells be painted black so that (i) the number of each row (resp. each column) is
the number of black cells in the row (resp. column), and (ii) the cells of each tile are all
black or all left uncolored?

A tile is a set of cells connected through orthogonally adjacent cells of the same tile. The
grid with `h` rows and `w` columns is Mathlib's grid graph `pathGraph h □ pathGraph w` on
`Fin h × Fin w`; keeping only its edges inside tiles gives `tileGraph`.

The instance lists the rows of the grid, top to bottom, each entry the name (a natural number)
of the tile containing the cell, followed by the row numbers, top to bottom, and the column
numbers, left to right.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TILEPAINT is NP-complete.** Source: Iwamoto and Ide (2022), Theorem 1. -/
public theorem_wanted tilepaint_npComplete :
    tilepaintDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tilepaintDec

end MetaMathlibExt.Complexity.NPComplete.Tilepaint
