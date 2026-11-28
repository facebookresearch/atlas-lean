/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RIPPLE EFFECT is NP-complete

Source:
Y. Takenaga, S. Aoyagi, S. Iwata and T. Kasai, "Shikaku and ripple effect are NP-complete",
Congressus Numerantium 216 (2013), 119-127, MR3220078;
puzzle rules: Nikoli Co., Ltd., "Ripple Effect", https://www.nikoli.co.jp/en/puzzles/ripple_effect/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RippleEffectDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RippleEffect

/-!
# RIPPLE EFFECT is NP-complete

Ripple Effect (Nikoli) is played on a rectangular grid divided by bold lines into areas called
rooms; some cells contain numbers. Nikoli's rules: "The areas divided by bold lines are called
'Rooms'. Fill in all empty cells with numbers under the following rules. Each Room contains
consecutive numbers starting from 1. If a number is duplicated in a row or a column, the space
between the duplicated numbers must be equal to or larger than the value of the number."
Takenaga, Aoyagi, Iwata and Kasai (2013) prove that deciding whether a Ripple Effect instance
has a solution is NP-complete.

INSTANCE: an `m × n` grid divided into connected rooms, some cells containing numbers.
QUESTION: can the empty cells be filled so that a room of `k` cells holds the numbers
`1, …, k`, and any two cells of one row or column holding the same number `d` have at least
`d` cells between them?

Representation. The grid is given row by row; a cell is a pair `(k, g)` of its room label `k`
and its number `g` (`0` for an empty cell), so the instance size is proportional to the area
plus the binary length of the entries. A room is the set of cells with one label; `WellFormed`
requires every room to be connected (`SimpleGraph.Preconnected` of the subgraph that Mathlib's
grid graph `pathGraph m □ pathGraph n` induces on it). A filling is a function `ℕ → ℕ → ℕ` read
on the grid that keeps the given numbers. "Consecutive numbers starting from 1" in a room of
`k` cells means the numbers `1, …, k`, each once: every number lies in `[1, k]` and no number
repeats in the room. Cells `(r, c)` and `(r, c')`, `c < c'`, have `c' - c - 1` cells between
them, so the spacing rule reads `c + d < c'`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RIPPLE EFFECT is NP-complete.** Source: Takenaga, Aoyagi, Iwata and Kasai (2013). -/
public theorem_wanted rippleEffect_npComplete :
    rippleEffectDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rippleEffectDec

end MetaMathlibExt.Complexity.NPComplete.RippleEffect
