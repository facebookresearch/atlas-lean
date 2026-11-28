/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MOON-OR-SUN is NP-complete

Source:
C. Iwamoto and T. Ide, "Moon-or-Sun, Nagareru, and Nurimeizu are NP-complete",
IEICE Transactions on Fundamentals of Electronics, Communications and Computer Sciences
E105-A(9) (2022), 1187-1194, doi:10.1587/transfun.2021DMP0006;
puzzle rules: Nikoli Co., Ltd., "Moon-or-Sun",
https://www.nikoli.co.jp/en/puzzles/moon_or_sun/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MoonOrSunDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MoonOrSun

/-!
# MOON-OR-SUN is NP-complete

Moon-or-Sun (Nikoli) is played on a rectangular grid divided by bold lines into rooms; some
cells contain a moon and some a sun. Nikoli's rules:
1. Draw a line to make a single loop. Lines pass through the centers of cells, horizontally,
   vertically, or turning. The loop never crosses itself, branches off, or goes through the same
   cell twice.
2. The loop goes through each room only one time. Once the loop leaves a room, it cannot return
   to enter this room.
3. In each room, the loop goes through all of the moon cells or all of the sun cells. The loop
   cannot pass through both moon cells and sun cells in one room.
4. After the loop goes through the moons in one room it has to go through all the suns in the
   next room it enters, and vice versa.

INSTANCE: a rectangular grid divided into rooms, with some cells marked moon or sun.
QUESTION: is there a loop satisfying rules 1-4? (Iwamoto and Ide 2022 prove this
NP-complete.)

The grid is given row by row: entry `c` of row `r` is `(room, mark)` for cell `(r, c)`, with
mark `0` (empty), `1` (moon) or `2` (sun); rooms are `0, …, R - 1`. `WellFormed` requires
`m, n ≥ 1` rows and columns, rows of equal length, room indices below `R`, marks at most `2`,
and every room a nonempty connected set of cells (the region a closed bold boundary encloses).
Rooms need not be rectangles: Nikoli's English text calls a room "a rectangle, bordered by bold
lines", but the sample puzzle on the same rules page has L-shaped and Z-shaped rooms.

Cells are `Fin m × Fin n`, adjacent when they share a side in Mathlib's grid graph
`pathGraph m □ pathGraph n`. Rule 1 is a cycle `c` of the grid graph
(`SimpleGraph.Walk.IsCycle`). Rule 2: the cycle meets every room, and enters each room (moves
from a cell outside it to a cell inside it) at most once. Rules 3 and 4: each room gets a type,
`true` (moon) or `false` (sun); a moon cell lies on the cycle exactly when its room has type
moon, and a sun cell exactly when its room has type sun; and each move of the cycle from one
room into another changes the type. A room without moons or suns may take either type.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MOON-OR-SUN is NP-complete.** Source: Iwamoto and Ide (2022). -/
public theorem_wanted moonOrSun_npComplete :
    moonOrSunDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L moonOrSunDec

end MetaMathlibExt.Complexity.NPComplete.MoonOrSun
