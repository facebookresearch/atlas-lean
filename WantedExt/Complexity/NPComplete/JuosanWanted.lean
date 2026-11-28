/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JUOSAN is NP-complete

Source:
C. Iwamoto and T. Ibusuki, "Polynomial-time reductions from 3SAT to Kurotto and Juosan puzzles",
IEICE Transactions on Information and Systems E103-D(3) (2020), 500-505,
doi:10.1587/transinf.2019FCP0004 (Section 1: the rules and the decision problem; Theorem 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.JuosanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Juosan

open MetaMathlibExt.Complexity.NPComplete.Heyawake (HeyawakeInstance rows cols roomOf WellFormed)

/-!
# JUOSAN is NP-complete

Juosan is played on a rectangular grid of cells divided into rectangular territories; each
territory contains a number or no number. Every cell is filled with a `−`-mark or a `|`-mark so
that (Iwamoto and Ibusuki, Section 1):
1. "The number in a territory shows the number of `−`-marks if `−`-marks have majority, or the
   number of `|`-marks if `|`-marks have majority. However, there are also cases where the
   numbers of `−`-marks and `|`-marks are the same. Territories with no numbers may have any
   number of `−`-marks and `|`-marks."
2. "`−`-marks can extend across more than three cells horizontally, but not more than two cells
   vertically."
3. "`|`-marks can extend across more than three cells vertically, but not more than two cells
   horizontally."

INSTANCE: a rectangular grid of cells divided into rectangular territories, each with a number
or no number. QUESTION: is there a solution? (Theorem 1: the Juosan puzzle problem is
NP-complete.)

Rule 1 says that the number is the larger of the two counts (with a tie, both counts equal
it). Rules 2 and 3 forbid three vertically consecutive `−`-marks and three horizontally
consecutive `|`-marks.

The grid is given explicitly, as in `WantedExt.Complexity.NPComplete.HeyawakeWanted`, whose
instance, `rows`, `cols`, `roomOf` and `WellFormed` are reused: entry `c` of row `r` is the
index of the territory (Heyawake's room) containing cell `(r, c)`, and territory `k` carries
`(numbered, number)`; `WellFormed` requires a nonempty grid with rows of equal length,
territory indices in range, and every territory nonempty and rectangular. A filling is a
function `ℕ → ℕ → Bool` read on the grid, `true` for a `−`-mark and `false` for a `|`-mark.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **JUOSAN is NP-complete.** Source: Iwamoto and Ibusuki (2020), Theorem 1. -/
public theorem_wanted juosan_npComplete :
    juosanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L juosanDec

end MetaMathlibExt.Complexity.NPComplete.Juosan
