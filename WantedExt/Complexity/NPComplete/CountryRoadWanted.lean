/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COUNTRY ROAD is NP-complete

Source:
A. Ishibashi, Y. Sato and S. Iwata, "NP-completeness of two pencil puzzles: Yajilin and Country
Road", Utilitas Mathematica 88 (2012), 237-246;
H. Tang, "A framework for loop and path puzzle satisfiability NP-hardness results",
arXiv:2202.02046 (2022), Section 3.7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CountryRoadDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CountryRoad

/-!
# COUNTRY ROAD is NP-complete

Country Road (Nikoli) is played on a rectangular grid divided into regions, some of which carry
a number. Tang (2022, Section 3.7) states its rules: "Draw a single loop passing between
adjacent cell centres and visiting each region once. A number within a region indicates the
number of cells in that region through which the loop passes. Out of any pair of adjacent cells
in different regions, at least one must be used by the loop."

INSTANCE: a rectangular grid partitioned into regions, each a connected set of cells, some
regions carrying a number.
QUESTION: is there a loop satisfying these rules?

Ishibashi, Sato and Iwata (2012) prove this NP-complete; Tang (2022, Section 3.7) reproves
NP-hardness with a T-metacell gadget and notes that a solution is checked in polynomial time.

Representation. The grid is given explicitly, row by row: entry `c` of row `r` is the region of
cell `(r, c)`, and the regions are `0, …, R - 1`, where `R` is the length of the list of region
numbers; entry `k` of that list is `0` when region `k` has no number and `v + 1` when it carries
the number `v`. The grid is explicit, so its area is at most the encoded input length.
`WellFormed` requires at least one row and one column, rows of equal length, region indices
below `R`, and every region a nonempty connected set of cells (as in
`WantedExt.Complexity.NPComplete.MoonOrSunWanted`). Cells are `Fin m × Fin n`, adjacent when
they share a side in Mathlib's grid graph `pathGraph m □ pathGraph n`. The loop through cell
centres is a cycle `c` of this graph (`SimpleGraph.Walk.IsCycle`); its cells, the cells the loop
passes through or uses, are `c.support`. The loop visits each region once: it meets every
region, and enters each region (moves from a cell outside it to a cell inside it, a dart of `c`)
at most once, so its cells in each region form one contiguous stretch of the loop (the loop never
enters a region only when it lies inside that one region).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COUNTRY ROAD is NP-complete.** Source: Ishibashi, Sato and Iwata (2012); Tang (2022),
Section 3.7. -/
public theorem_wanted countryRoad_npComplete :
    countryRoadDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L countryRoadDec

end MetaMathlibExt.Complexity.NPComplete.CountryRoad
