/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STATIC PUZZNIC SOLVABILITY (CUBIC) is NP-complete

Source:
J. Anderson, L. M. Hvattum and A. Z. Salamon, "Puzznic is PSPACE-complete", arXiv:2610.23639
(2026), Section 1.1 (rules) and Theorem 1 ("Static Puzznic Solvability is NP-complete"; hardness
Theorem 3, membership Theorem 8);
J. Espasa, I. P. Gent, I. Miguel, P. Nightingale, A. Z. Salamon and M. Villaret,
"Cross-paradigm modelling: A case study of Puzznic", 23rd Workshop on Constraint Modelling and
Reformulation (ModRef 2024), Sections 2 and 3 (rules and their PDDL model) and Section 2.1
(membership in NP); journal-length version "Cross-paradigm modelling: A study of Puzznic", IEEE
36th International Conference on Tools with Artificial Intelligence (ICTAI 2024), 89-95,
doi:10.1109/ICTAI62512.2024.00021;
E. Friedman, "The game of Cubic is NP-complete", 34th Florida MAA Section Meeting (2001).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StaticPuzznicDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StaticPuzznic

/-!
# STATIC PUZZNIC SOLVABILITY (CUBIC) is NP-complete

Puzznic is a falling-block puzzle (Taito, 1989); its static variant, without moving wall blocks,
is also known as Cubic. Espasa et al. (Section 2): "Each cell may be empty, filled with a wall or
contain a patterned block. ... A selected block can be moved horizontally left or right if the cell
in the direction chosen is empty. Patterned blocks are affected by gravity, and fall until coming
to rest above another non-empty block or a wall. ... When two or more blocks with the same pattern
are adjacent horizontally or vertically, they match and are removed from play. The only exception
to this is when a patterned block is falling: it cannot match another block until it comes to
rest. ... The goal is to remove all patterned blocks from the grid." Anderson, Hvattum and Salamon
(Section 1.1) state the same rules ("If a block is not supported below by another block or a wall,
it falls one position per time step until it is supported"; blocks are destroyed "only when all
blocks are supported").

INSTANCE: a rectangular grid in which each cell is empty, a wall, or a patterned block with a
pattern.
QUESTION: is there a sequence of player moves after which no patterned block remains?

The steps of play are those of the PDDL model of Espasa et al. (Section 3): if some block has an
empty cell directly below it ("falling_flag"), the only possible step moves one such block one cell
down ("fall_block"); otherwise, if two orthogonally adjacent blocks have the same pattern
("matching_flag"), the only possible step removes, all at once, every block that has an
orthogonally adjacent block with its pattern ("match_blocks"); otherwise the player moves one block
one cell left or right into an empty cell ("move_block"). The goal is a grid with no patterned
block. Cells outside the grid are not locations of the model, so no block moves, falls or matches
into them; they read as walls here.

Representation. The grid is the list of its rows from top to bottom, each the list of its cells
from left to right: code `0` is an empty cell, `1` a wall, and `p + 2` a patterned block with
pattern `p`. Cell `(r + 1, c)` is directly below cell `(r, c)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STATIC PUZZNIC SOLVABILITY (CUBIC) is NP-complete.** Source: Anderson, Hvattum and Salamon
(2026), Theorem 1; Espasa et al. (2024); Friedman (2001). -/
public theorem_wanted staticPuzznic_npComplete :
    staticPuzznicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L staticPuzznicDec

end MetaMathlibExt.Complexity.NPComplete.StaticPuzznic
