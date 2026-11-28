/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLICKOMANIA with two colors and two columns is NP-complete

Source:
A. Adler, E. D. Demaine, A. Hesterberg, Q. Liu and M. Rudoy, "Clickomania is hard, even with
two colors and columns", in J. Beineke and J. Rosenhouse (eds.), *The Mathematics of Various
Entertaining Subjects, Vol. 2*, Princeton University Press (2017),
doi:10.23943/princeton/9780691171920.003.0018, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ClickomaniaTwoColorsTwoColumnsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClickomaniaTwoColorsTwoColumns

open MetaMathlibExt.Complexity.NPComplete.Clickomania

/-!
# CLICKOMANIA with two colors and two columns is NP-complete

INSTANCE: a rectangular board with at most two columns, initially full of square blocks, each
colored one of at most two colors.
QUESTION: can all blocks be removed by Clickomania moves (click a group of at least two blocks;
the group disappears, blocks above fall, empty columns are removed)?

This is CLICKOMANIA (`ClickomaniaWanted`, the rules of Biedl et al.) restricted to the class
`Clickomania(2, 2)` of Adler, Demaine, Hesterberg, Liu and Rudoy (Section 2: "a grid of tiles
with at most `w` columns and `c` different colors"), which they prove NP-complete (Theorem 1);
their construction is "perfectly rectangular in shape" (Section 4.1), so the parent's
rectangular, initially full boards suffice. The board, the moves and the question are the
parent's (`Clickomania.Board`, `Clickomania.Move`, `Clickomania.ClickomaniaFeasible`);
`WellFormed` is the parent's plus the restriction: at most two columns, and every block has
one of two colors `a` and `b`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLICKOMANIA with two colors and two columns is NP-complete.** Source: Adler, Demaine,
Hesterberg, Liu and Rudoy (2017), Theorem 1. -/
public theorem_wanted clickomaniaTwoColorsTwoColumns_npComplete :
    clickomaniaTwoColorsTwoColumnsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L clickomaniaTwoColorsTwoColumnsDec

end MetaMathlibExt.Complexity.NPComplete.ClickomaniaTwoColorsTwoColumns
