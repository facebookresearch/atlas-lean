/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EYE-WITLESS is NP-complete

Source:
H. Tang, "On the NP-completeness of satisfying certain path and loop puzzles",
arXiv:2004.12849 (2020), Sections 1.1 and 3.1;
puzzle rules: TheGreatEscaper, "The Ludicrous Loop: over a thousand cells of circular logic",
https://puzzling.stackexchange.com/q/52899/ (2017).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EyeWitlessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EyeWitless

/-!
# EYE-WITLESS is NP-complete

Tang (2020), Section 1.1: "In Eye-Witless, the player is given a rectangular grid, and the aim
is to draw a loop passing orthogonally through the centres of its cells. Some eyes have been
given with different colours: all eyes must be passed through by the loop. Additionally, if we
consider the loop as a corridor with width one cell, same-coloured eyes can see the same
distances, at the same relative directions. For example, if at a blue eye the loop turns,
extending 3 cells down and 2 cells left before turning, at every blue eye the loop must go 3
cells before turning on the clockwise side of the bend, and 2 cells on the other side". The
original rules (TheGreatEscaper 2017): "The loop must pass over every eye. The eyes can see
along loop segments until they turn. Same coloured eyes must see the same thing; [...] If they
have white pupils, they may see rotations of each other." Tang proves that deciding whether an
Eye-Witless puzzle has a solution is NP-complete (Section 3.1).

INSTANCE: a rectangular grid, some cells holding eyes of given colours.
QUESTION: is there a loop through the centres of cells, passing every eye, such that any two eyes
of the same colour see the same thing up to a rotation?

Representation. The grid is given row by row: entry `c` of row `r` is `0` for a cell without
an eye and `k + 1` for an eye of colour `k`, so the instance size is proportional to the area
plus the binary length of the colours. Cells are `Fin m × Fin n`, adjacent when they share a
side in Mathlib's grid graph `pathGraph m □ pathGraph n`; the loop is a cycle of this graph
(`SimpleGraph.Walk.IsCycle`) whose support contains every eye. Directions are `0` up, `1` right,
`2` down, `3` left. What an eye at `x` sees (`view`) is the list of its four arms, the arm in
direction `d` being the number of consecutive loop edges going straight from `x` in direction
`d` (so `0` when the loop does not leave `x` that way): the loop leaves `x` along two arms and
turns where each arm ends. A rotation by a quarter turn sends up to right, right to down, down
to left and left to up, so it acts on a view as a cyclic shift (`List.rotate`); two eyes of the
same colour must have views that differ by such a shift. Reflections are not allowed: they
would move the longer arm of a bend to the other side ("the clockwise side of the bend").

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EYE-WITLESS is NP-complete.** Source: Tang (2020), Section 3.1. -/
public theorem_wanted eyeWitless_npComplete :
    eyeWitlessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L eyeWitlessDec

end MetaMathlibExt.Complexity.NPComplete.EyeWitless
