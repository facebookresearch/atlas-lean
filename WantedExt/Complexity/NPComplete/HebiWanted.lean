/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HEBI is NP-complete

Source:
S. Kanehiro and Y. Takenaga, "Satogaeri, Hebi, and Suraromu are NP-complete", Proc. 3rd
International Conference on Applied Computing and Information Technology / 2nd International
Conference on Computational Science and Intelligence (ACIT-CSI 2015), IEEE (2015),
doi:10.1109/ACIT-CSI.2015.17;
puzzle rules: Nikoli Co., Ltd., "Hebi Ichigo", https://www.nikoli.co.jp/en/puzzles/hebi/ and
https://www.nikoli.co.jp/ja/puzzles/hebi/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HebiDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Hebi

/-!
# HEBI is NP-complete

Hebi (Hebi Ichigo, Nikoli) is played on a rectangular grid of white and black squares; some
black squares carry a number and an arrow. Nikoli's English rules:
1. "Place numbers in squares (parts of snakes) so that the figures from 1 (head) to 5 (tail) are
   sequentially connected one by one in the white squares."
2. "Snakes cannot touch (share a side with) other snakes".
3. "Seen from the 2→1 direction of a snake (the snake's direction of view), a part of another
   snake can not be in the squares to the next black square or to the rim of the grid."
4. "The numbers in the black squares show the number in the nearest square in the direction of
   the arrow. 0 shows that there is no snake from this square to the next black square or outer
   rim."
Nikoli's Japanese rules place "some" (いくつか) snakes, each a piece of the numbers 1 to
5 connected in order vertically and horizontally; a solution has at least one snake. Kanehiro
and Takenaga (2015) prove Hebi NP-complete.

INSTANCE: a rectangular grid of white and black squares, some black squares carrying a number
and an arrow.
QUESTION: can one or more snakes be placed in the white squares so that rules 1-4 hold?

Representation. The grid is given row by row, so the instance size is proportional to its area
plus the binary length of the numbers. A square is `(b, v, d)`: black if `b = true`; a black
square with `v ≥ 1` carries the number `v - 1` and an arrow in direction `d` (`0` up, `1` right,
`2` down, `3` left), and `v = 0` means no number. Squares are pairs `(row, column)`. A snake is
the list of its five squares from head (`1`) to tail (`5`): distinct white squares, consecutive
ones sharing a side. Snakes are listed in some order; different snakes share no square and no
side. The squares a square `x` sees in direction `d` (`ray`) are the squares at distance
`1, 2, …` from `x` in that direction, up to the next black square or the rim. A snake looks in
the direction from its square `2` to its head. The number in a square (`numberAt`) is its place
on the snake through it, `0` if no snake passes; the nearest number seen in a direction is the
first nonzero number along the ray, `0` if there is none.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HEBI is NP-complete.** Source: Kanehiro and Takenaga (2015). -/
public theorem_wanted hebi_npComplete :
    hebiDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hebiDec

end MetaMathlibExt.Complexity.NPComplete.Hebi
