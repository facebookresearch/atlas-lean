/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

/-!
# STATIC PUZZNIC SOLVABILITY (CUBIC): definitions

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

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StaticPuzznic

/-- An instance: the rows of the grid from top to bottom, each a list of cell codes (`0` empty,
`1` wall, `p + 2` a block with pattern `p`). -/
abbrev StaticPuzznicInstance := List (List ℕ)

/-- The code of cell `(r, c)` (row `r` from the top, column `c` from the left); a cell outside the
grid reads as a wall. -/
def cell (B : List (List ℕ)) (r c : ℕ) : ℕ := (B.getD r []).getD c 1

/-- Cell `(r, c)` holds a patterned block. -/
def IsBlock (B : List (List ℕ)) (r c : ℕ) : Prop := 2 ≤ cell B r c

/-- The grid with the block at `(r, c)` moved to `(r', c')`. -/
def moveBlock (B : List (List ℕ)) (r c r' c' : ℕ) : List (List ℕ) :=
  let B₀ := B.set r ((B.getD r []).set c 0)
  B₀.set r' ((B₀.getD r' []).set c' (cell B r c))

/-- Some block has an empty cell directly below it ("falling_flag"). -/
def Falling (B : List (List ℕ)) : Prop :=
  ∃ r c, IsBlock B r c ∧ cell B (r + 1) c = 0

/-- The block at `(r, c)` has an orthogonally adjacent block with the same pattern. -/
def HasTwin (B : List (List ℕ)) (r c : ℕ) : Prop :=
  IsBlock B r c ∧ (cell B (r + 1) c = cell B r c ∨ cell B r (c + 1) = cell B r c ∨
    (0 < r ∧ cell B (r - 1) c = cell B r c) ∨ (0 < c ∧ cell B r (c - 1) = cell B r c))

/-- `HasTwin` compares cell codes, so it is decidable. -/
instance (B : List (List ℕ)) (r c : ℕ) : Decidable (HasTwin B r c) :=
  inferInstanceAs (Decidable (2 ≤ cell B r c ∧ (cell B (r + 1) c = cell B r c ∨
    cell B r (c + 1) = cell B r c ∨ (0 < r ∧ cell B (r - 1) c = cell B r c) ∨
    (0 < c ∧ cell B r (c - 1) = cell B r c))))

/-- Two orthogonally adjacent blocks have the same pattern ("matching_flag"). -/
def Matching (B : List (List ℕ)) : Prop :=
  ∃ r c, HasTwin B r c

/-- The grid with every block that has an orthogonally adjacent block of its pattern removed
("match_blocks"). -/
def matchRemove (B : List (List ℕ)) : List (List ℕ) :=
  B.mapIdx fun r row => row.mapIdx fun c v => if HasTwin B r c then 0 else v

/-- One step of play from `B` to `B'`: a block with an empty cell below falls one cell; or, when
no block can fall and two adjacent blocks match, all matching blocks are removed; or, when neither
happens, a block moves one cell left or right into an empty cell. -/
def Step (B B' : List (List ℕ)) : Prop :=
  (∃ r c, IsBlock B r c ∧ cell B (r + 1) c = 0 ∧ B' = moveBlock B r c (r + 1) c) ∨
    (¬ Falling B ∧ Matching B ∧ B' = matchRemove B) ∨
    (¬ Falling B ∧ ¬ Matching B ∧ ∃ r c c', IsBlock B r c ∧ (c' = c + 1 ∨ c' + 1 = c) ∧
      cell B r c' = 0 ∧ B' = moveBlock B r c r c')

/-- Well-formedness of an instance: the grid is rectangular (all rows have the same length). -/
def WellFormed (i : StaticPuzznicInstance) : Prop :=
  ∀ row ∈ i, row.length = (i.headD []).length

/-- Some sequence of steps from the initial grid reaches a grid with no patterned block. -/
def StaticPuzznicFeasible (i : StaticPuzznicInstance) : Prop :=
  ∃ B, Relation.ReflTransGen Step i B ∧ ∀ r c, ¬ IsBlock B r c

open Classical in
/-- STATIC PUZZNIC SOLVABILITY as a decision problem over bitstrings. -/
noncomputable def staticPuzznicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StaticPuzznicInstance) x with
  | some i => decide (WellFormed i ∧ StaticPuzznicFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StaticPuzznic
