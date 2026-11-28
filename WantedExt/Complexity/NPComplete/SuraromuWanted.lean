/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SURAROMU is NP-complete

Source:
S. Kanehiro and Y. Takenaga, "Satogaeri, Hebi, and Suraromu are NP-complete", Proc. 3rd
International Conference on Applied Computing and Information Technology / 2nd International
Conference on Computational Science and Intelligence (ACIT-CSI 2015), IEEE (2015),
doi:10.1109/ACIT-CSI.2015.17;
puzzle rules: Nikoli Co., Ltd., "Suraromu", https://www.nikoli.co.jp/en/puzzles/suraromu/ and
https://www.nikoli.co.jp/ja/puzzles/suraromu/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SuraromuDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Suraromu

/-!
# SURAROMU is NP-complete

Suraromu (Nikoli) is played on a rectangular grid of white and black cells, with one white cell
holding a numbered open circle, and dashed lines called gates. Nikoli's English rules:
1. "Make a single loop with lines passing through the centers of cells, horizontally,
   vertically, or changing direction. The loop never crosses itself, branches off, or goes
   through the same cell twice."
2. "The continuous dotted lines between black cells or to the outer frame are 'Gates.' The loop
   must pass all Gates, but a Gate can only be passed once."
3. "The loop starts from the cell with the open numbered circle and returns to this cell. The
   number in the open circle shows the number of Gates to go through."
4. "Numbers at the ends of Gates – in the black cells – show when the loop crosses the Gate. A
   Gate without a number may be crossed at any point in the loop. For example, a Gate with a '1'
   must be the first crossed (in one of the directions) from the cell with the open circle."
Nikoli's Japanese rules add that the loop is drawn in white cells, that it crosses every gate
once at a right angle and touches a gate nowhere else, and that the circle's number is the
total number of gates.

INSTANCE: a Suraromu grid: black cells, the circle cell with its number, and the gates with
their optional order numbers.
QUESTION: is there a loop satisfying rules 1-4? (Kanehiro and Takenaga 2015 prove this
NP-complete.)

Representation. The board is given explicitly, row by row (`true` = black cell), so the instance
size is proportional to the area of the board. Cells are `Fin m × Fin n` (row, column), adjacent
when they share a side in Mathlib's grid graph `pathGraph m □ pathGraph n`. A gate `(r, c, ℓ, v,
k)` covers the `ℓ ≥ 1` white cells `(r + t, c)` (vertical gate, `v = true`) or `(r, c + t)`
(horizontal gate, `v = false`) for `t < ℓ`; `WellFormed` requires that the cells just beyond
both ends are black or outside the grid, so a gate runs between black cells or to the frame. `k`
is the number written at the gate's ends, `0` when it has none. Rule 1 is a cycle `c` of the
grid graph (`SimpleGraph.Walk.IsCycle`) through white cells only; rule 3 makes it start and end
at the circle cell. Rule 2: exactly one cell of each gate lies on the loop. Since a gate is
closed off at both ends, the loop then crosses the gate at a right angle and touches it nowhere
else: a loop that went along the gate from its one gate cell would enter a second gate cell, a
black cell, or leave the grid. Rule 4: listing the gates in the order the loop crosses them from
the circle cell (`crossings`), either that list or its reverse (the other direction) has the
gate numbered `k` in position `k`. `WellFormed` keeps the circle cell off every gate, since the
order "from the cell with the open circle" is undefined for a gate through that cell. Each gate
is listed once. A horizontal and a vertical gate may share a cell, as the rules do not forbid
it; no loop satisfying rule 2 passes such a cell, since each of its horizontal neighbors is on
the horizontal gate, black or outside the board, and each vertical neighbor likewise on the
vertical gate, so a loop neighbor would put a second cell of one gate on the loop. Hence the
order in which `crossings` lists the two gates at a shared cell never matters.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SURAROMU is NP-complete.** Source: Kanehiro and Takenaga (2015). -/
public theorem_wanted suraromu_npComplete :
    suraromuDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L suraromuDec

end MetaMathlibExt.Complexity.NPComplete.Suraromu
