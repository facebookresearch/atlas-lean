/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PIPE MANIA is NP-complete

Source:
G. Viglietta, "Gaming is a hard job, but someone has to do it!", Theory of Computing Systems
54(4) (2014), 595-621, doi:10.1007/s00224-013-9497-5, Section 3.7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PipeManiaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PipeMania

/-!
# PIPE MANIA is NP-complete

Viglietta (2014), Section 3.7, "Pipe Mania (The Assembly Line, 1989) is NP-complete": "in this
puzzle game a long-enough pipe has to be constructed out of several pieces, randomly presented
in a queue, starting from a given source location. After a timer expires, a stream of water
starts flowing from the source into the pipes, and the game is won if and only if the stream
traverses a given number of tiles before spilling out. Since the player can keep constructing
pipes on the same tile, 'overwriting' the previous pieces until he gets the piece that he wants,
he may indeed shape the pipe as he pleases, if the initial timer lasts long enough. Some
obstacles are also present in each level, such as fire hydrants, on which pipes cannot be
built." The reduction lets the pipe cover most tiles twice using cross-shaped pieces, and
measures the pipe's length counting such a tile twice.

INSTANCE: a rectangular board of tiles, some of them obstacles; a source tile with the direction
of its outlet; a number `N`.
QUESTION: can pipe pieces be placed on free tiles so that the stream from the source traverses
`N` tiles before spilling out?

Representation. The board is given row by row (`true` = obstacle), so the instance size is
proportional to its area plus the binary length of `N`. Tiles are pairs `(row, column)`;
directions are `0` up, `1` right, `2` down, `3` left. The pieces are Pipe Mania's straight
pieces, the four elbows, and the cross; each piece other than the cross joins two different
sides of its tile, and the cross joins left with right and top with bottom. Since the player
shapes the pipe freely, a placement is described by the stream's route: the list of the `N`
tiles it traverses after leaving the source, in order, a tile traversed twice listed twice.
Such a list is realized by a placement exactly when the first tile is the source's neighbor in
the outlet direction; consecutive tiles share a side; every listed tile is a free tile of the
board other than the source; the stream never leaves a tile through the side it entered by (no
piece joins a side to itself); and every tile is traversed at most once, or twice through a
cross: both passes straight, one horizontal and one vertical (the second pass may be the last
traversal, whose exit side is then the side opposite its entry). The tiles after the last
traversal play no role, as the stream may spill out there.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PIPE MANIA is NP-complete.** Source: Viglietta (2014), Section 3.7. -/
public theorem_wanted pipeMania_npComplete :
    pipeManiaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pipeManiaDec

end MetaMathlibExt.Complexity.NPComplete.PipeMania
