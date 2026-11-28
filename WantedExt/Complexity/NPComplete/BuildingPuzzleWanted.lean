/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BUILDING PUZZLE (SKYSCRAPERS) is NP-complete

Source:
C. Iwamoto and Y. Matsui, "Computational complexity of building puzzles", IEICE Transactions
on Fundamentals of Electronics, Communications and Computer Sciences E99-A(6) (2016),
1145-1148, doi:10.1587/transfun.E99.A.1145;
problem statement as summarized in K. Haraguchi and R. Tanaka, "The building puzzle is still
hard even in the single lined version", Journal of Information Processing 25 (2017), 730-734,
doi:10.2197/ipsjjip.25.730.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BuildingPuzzleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BuildingPuzzle

/-!
# BUILDING PUZZLE (SKYSCRAPERS) is NP-complete

The Building puzzle (Skyscrapers) is played on an `n × n` grid of cells, with some Building
numbers in `[n] = {1, …, n}` written next to the ends of the rows and columns (a line has two
ends, so there are at most `4n` Building numbers). A solution fills all `n²` cells with integers
in `[n]` so that

* the integers form an `n × n` Latin square (in each row and column every integer in `[n]`
  appears exactly once), and
* the Building condition holds: reading each cell as a building of that height, for every
  Building number `b` one sees exactly `b` buildings when looking along its line from the end
  where `b` is written; a building is hidden by any higher building in front of it.

INSTANCE: an `n × n` Building puzzle instance and an `n × n` partial Latin square `S`.
QUESTION: is there a solution to the instance that extends `S`?
(Haraguchi and Tanaka 2017, Section 1, state the problem in this form as the one Iwamoto and
Matsui 2016 prove NP-complete.)

The grid part reuses `LatinSquareCompletion`: `n` and the partial square `S`, row by row, with
`0` for a blank cell. The Building numbers are four lists of length `n`, with `0` for no
number: `top`/`bottom` entry `c` is written above/below column `c`, and `left`/`right` entry
`r` to the left/right of row `r`. `WellFormed` asks for `LatinSquareCompletion.WellFormed`
(`n ≥ 1`, an `n × n` grid with entries at most `n`), no nonzero integer repeated in a row or
column of `S` (a partial Latin square; the blank `0` may repeat), and Building numbers at most
`n`.

A building is seen from an end of its line exactly when it is higher than every building
between it and that end, so the number of buildings seen is the number of such cells.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open LatinSquareCompletion

/-- **BUILDING PUZZLE (SKYSCRAPERS) is NP-complete.** Source: Iwamoto and Matsui (2016);
statement as in Haraguchi and Tanaka (2017). -/
public theorem_wanted buildingPuzzle_npComplete :
    buildingPuzzleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L buildingPuzzleDec

end MetaMathlibExt.Complexity.NPComplete.BuildingPuzzle
