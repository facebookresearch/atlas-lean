/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STATIC PUZZNIC SOLVABILITY (CUBIC): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

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
