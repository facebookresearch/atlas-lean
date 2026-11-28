/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHIKAKU is NP-complete

Source:
Y. Takenaga, S. Aoyagi, S. Iwata and T. Kasai, "Shikaku and ripple effect are NP-complete",
Congressus Numerantium 216 (2013), 119-127, MR3220078;
puzzle rules: Nikoli Co., Ltd., "Shikaku", https://www.nikoli.co.jp/en/puzzles/shikaku/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShikakuDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Shikaku

/-!
# SHIKAKU is NP-complete

Shikaku (Nikoli) is played on a rectangular grid, some of whose cells contain numbers. Nikoli's
rules: "Divide the grid into rectangles with the numbers in the cells. Each rectangle is to
contain only one number showing the number of cells in the rectangle." Takenaga, Aoyagi, Iwata
and Kasai (2013) prove that deciding whether a Shikaku instance has a solution is
NP-complete.

INSTANCE: an `m × n` grid, some cells containing positive integers.
QUESTION: can the grid be divided into rectangles, each containing exactly one number, which
equals the number of cells of the rectangle?

Representation. The grid is given row by row: entry `c` of row `r` is `0` for an empty cell and
`k ≥ 1` for a cell containing `k`, so the instance size is proportional to the area plus the
binary length of the numbers. A rectangle `(r, c, h, w)` consists of the `h · w` cells
`(r + a, c + b)` with `a < h` and `b < w`; a division is a list of rectangles of positive height
and width inside the grid such that every cell lies in exactly one of them (so no rectangle is
listed twice).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHIKAKU is NP-complete.** Source: Takenaga, Aoyagi, Iwata and Kasai (2013). -/
public theorem_wanted shikaku_npComplete :
    shikakuDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shikakuDec

end MetaMathlibExt.Complexity.NPComplete.Shikaku
