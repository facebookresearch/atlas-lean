/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HERUGOLF is NP-complete

Source:
C. Iwamoto, M. Haruishi and T. Ibusuki, "Computational complexity of Herugolf and Makaro",
IEICE Transactions on Fundamentals of Electronics, Communications and Computer Sciences E102-A(9)
(2019), 1118-1125, doi:10.1587/transfun.E102.A.1118;
Nikoli, Herugolf rules, https://www.nikoli.co.jp/en/puzzles/herugolf/ (Japanese:
https://www.nikoli.co.jp/ja/puzzles/herugolf/).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HerugolfDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Herugolf

/-!
# HERUGOLF is NP-complete

INSTANCE: a rectangular grid in which some cells hold a ball (a circle with a positive number),
some cells are holes (H) and some cells are water hazards (gray cells); every other cell is
empty.

QUESTION: can every ball be moved by one or more shots into a hole, one ball per hole, following
Nikoli's rules?
* In its first shot a ball moves straight, horizontally or vertically, across exactly as many
  cells as its number; each later shot is one cell shorter, and its direction may change. A ball
  that has stopped in a hole, or whose next shot would have length `0`, moves no further.
* A ball may not leave the grid, and may not stop on a water hazard (it may fly over one).
* The arrows drawn for the shots may not pass over other balls or holes, and arrows (of the same
  or of different balls) may not cross or overlap.
* One ball is brought to every hole.

Iwamoto, Haruishi and Ibusuki (2019, abstract): "Herugolf and Makaro are Nikoli's pencil puzzles.
[...] It is shown that deciding whether a given instance of each puzzle has a solution is
NP-complete." The rules are those of Nikoli's rules page, quoted above in paraphrase; the paper's
full text was not available.

The board is given explicitly, row by row (`h` rows of `w` cells each), so its area is at most
the input length. Cell codes: `0` empty, `1` hole, `2` water hazard, and `k + 2` (`k ≥ 1`) a ball
with number `k`. Membership in NP: the shot directions of every ball are a certificate; the cells
a ball's arrows cover are distinct board cells, so it makes at most `w * h` shots and the
certificate has polynomial size.

Cells are integer points `(x, y)` (column `x < w`, row `y < h`). A solution gives each ball a
list of shot directions (`dir`: right, left, down, up); the `t`-th shot (from `0`) of a ball with
number `k` has length `k - t`. The arrow of a shot from cell `p` of length `ℓ` in direction `d`
covers `p + d, …, p + ℓ • d` and stops at `p + ℓ • d` (`shot`, `step`). `stops` lists the cells
where the shots stop and `path` the cells the arrows cover after the start, in order; its last
cell is the final stop. The rules become:
* at least one shot and at most `k` shots (so every shot has positive length);
* every covered cell is on the board, and no stop is on water;
* the final stop is a hole;
* every covered cell before the final stop is neither a hole nor a ball's cell, so the arrows do
  not pass over balls or holes, and a ball never stops in a hole before its final shot;
* the start cells of all balls together with all covered cells are pairwise distinct (no arrow
  crosses or overlaps another, nor revisits a cell of its own ball);
* every hole is the final stop of some ball.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HERUGOLF is NP-complete.** Source: Iwamoto, Haruishi and Ibusuki (2019). -/
public theorem_wanted herugolf_npComplete :
    herugolfDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L herugolfDec

end MetaMathlibExt.Complexity.NPComplete.Herugolf
