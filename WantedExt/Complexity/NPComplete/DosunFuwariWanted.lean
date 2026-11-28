/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOSUN-FUWARI is NP-complete

Source:
C. Iwamoto and T. Ibusuki, "Dosun-Fuwari is NP-complete", Journal of Information Processing 26
(2018), 358-361, doi:10.2197/ipsjjip.26.358.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DosunFuwariDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DosunFuwari

/-!
# DOSUN-FUWARI is NP-complete

INSTANCE: a rectangular grid of cells, partitioned into black cells and rooms.
QUESTION: can balloons and iron balls be placed in the cells of the rooms so that
(1) each room contains exactly one balloon and exactly one iron ball,
(2) every balloon is in the top row of the grid, or in a cell right under a black cell or right
under another balloon, and
(3) every iron ball is in the bottom row of the grid, or in a cell right over a black cell or
right over another iron ball?

A cell holds at most one object, and black cells hold none. A room is a region of the grid
surrounded by bold lines: a set of cells connected through orthogonally adjacent cells of the
same room. The grid with `h` rows and `w` columns is Mathlib's grid graph
`pathGraph h □ pathGraph w` on `Fin h × Fin w`; keeping only its edges inside rooms gives
`roomGraph`.

The instance lists the rows of the grid, top to bottom (row `0` is the top row); entry `0` is a
black cell and an entry `k ≥ 1` is a cell of room `k`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DOSUN-FUWARI is NP-complete.** Source: Iwamoto and Ibusuki (2018). -/
public theorem_wanted dosunFuwari_npComplete :
    dosunFuwariDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dosunFuwariDec

end MetaMathlibExt.Complexity.NPComplete.DosunFuwari
