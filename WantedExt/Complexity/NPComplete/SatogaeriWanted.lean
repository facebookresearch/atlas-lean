/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SATOGAERI is NP-complete

Source:
S. Kanehiro and Y. Takenaga, "Satogaeri, Hebi, and Suraromu are NP-complete", 2015 3rd
International Conference on Applied Computing and Information Technology / 2nd International
Conference on Computational Science and Intelligence (ACIT-CSI 2015), IEEE,
doi:10.1109/ACIT-CSI.2015.17;
puzzle rules: Nikoli Co., Ltd., "Satogaeri" (Japanese rules page),
https://www.nikoli.co.jp/ja/puzzles/satogaeri/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SatogaeriDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Satogaeri

/-!
# SATOGAERI is NP-complete

Satogaeri (Nikoli) is played on a rectangular grid divided by bold lines into regions
("countries"); some cells hold a circle, possibly with a number. Nikoli's rules (translated):
1. Move each circle straight, vertically or horizontally, so that every region bounded by bold
   lines contains exactly one circle.
2. The number in a circle is the number of cells it moves. For a circle without a number, how
   many cells it moves is not known; it may also not move.
3. A circle cannot move onto the track of another circle's move or onto a place where another
   circle is.

INSTANCE: a rectangular grid divided into regions, with some cells holding a circle (with or
without a number). QUESTION: can the circles be moved according to rules 1-3? (Kanehiro and
Takenaga 2015 prove this NP-complete; their full text was not available, so the rules follow
Nikoli's rules page.)

The grid is given row by row: entry `c` of row `r` is `(region, clue)` for cell `(r, c)`, with
clue `0` (no circle), `1` (circle without a number) or `d + 2` (circle with number `d`); regions
are `0, …, R - 1`. `WellFormed` requires at least one row and one column, rows of equal length,
region indices below `R`, and every region a nonempty connected set of cells (the region a
closed bold boundary encloses).

Cells are `Fin m × Fin n`. A solution sends each circle `x` to its destination `D x`, in the
row or the column of `x` (`D x = x` when it does not move); its track is the segment of cells
from `x` to `D x`, and it moves `|D x - x|` cells. Rule 3 says that the tracks of two different
circles, each including its start and end cell, are disjoint: a circle neither moves across or
onto another circle's track nor across or onto another circle's start or end cell. Rule 1 says
that every region contains the destination of exactly one circle.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SATOGAERI is NP-complete.** Source: Kanehiro and Takenaga (2015). -/
public theorem_wanted satogaeri_npComplete :
    satogaeriDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L satogaeriDec

end MetaMathlibExt.Complexity.NPComplete.Satogaeri
