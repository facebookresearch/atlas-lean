/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHAINED BLOCK: definitions

Source:
C. Iwamoto and T. Ide, "Chained Block is NP-complete", IEICE Transactions on Information and
Systems E107-D (2024), 320-324, doi:10.1587/transinf.2023FCL0001.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainedBlock

/-- An instance: the grid, as a list of rows of cell entries `(isBlack, k)`. -/
abbrev ChainedBlockInstance := List (List (Bool × ℕ))

/-- The number of rows. -/
abbrev rows (i : ChainedBlockInstance) : ℕ := i.length

/-- The number of columns: the length of the first row. -/
abbrev cols (i : ChainedBlockInstance) : ℕ := (i.headD []).length

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : ChainedBlockInstance) := Fin (rows i) × Fin (cols i)

/-- The entry of a cell. -/
def entry (i : ChainedBlockInstance) (p : Cell i) : Bool × ℕ :=
  (i.getD p.1 []).getD p.2 (false, 0)

/-- An initially black cell, holding a number or `?`. -/
def IsClue (i : ChainedBlockInstance) (p : Cell i) : Prop :=
  (entry i p).1 = true

/-- Well-formedness of an instance: the grid is rectangular, and cells that are not initially
black carry no number. -/
def WellFormed (i : ChainedBlockInstance) : Prop :=
  (∀ r ∈ i, r.length = cols i) ∧ ∀ r ∈ i, ∀ e ∈ r, e.1 = false → e.2 = 0

/-- Orthogonal adjacency of cells: the grid graph, the box product of two path graphs. -/
abbrev gridGraph (i : ChainedBlockInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The blocks of a set `B` of black cells: the connected components of the grid graph induced
on `B`. -/
abbrev Block (i : ChainedBlockInstance) (B : Set (Cell i)) :=
  ((gridGraph i).induce B).ConnectedComponent

/-- The cells of a block. -/
def blockCells {i : ChainedBlockInstance} {B : Set (Cell i)} (c : Block i B) : Set (Cell i) :=
  Subtype.val '' c.supp

/-- Diagonal neighbors: the cells differ by exactly one in both coordinates. -/
def CornerAdj {a b : ℕ} (p q : Fin a × Fin b) : Prop :=
  ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1) ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2)

/-- Two different blocks connected via corners. -/
def Touch {i : ChainedBlockInstance} {B : Set (Cell i)} (c d : Block i B) : Prop :=
  c ≠ d ∧ ∃ p ∈ blockCells c, ∃ q ∈ blockCells d, CornerAdj p q

/-- The graph on blocks whose edges join blocks connected via corners; a chain is a connected
component of it with at least two blocks. -/
def chainGraph (i : ChainedBlockInstance) (B : Set (Cell i)) : SimpleGraph (Block i B) :=
  SimpleGraph.fromRel (@Touch i B)

/-- The eight symmetries of the square lattice `ℤ × ℤ`: optionally swap the coordinates, then
optionally negate each coordinate. -/
def latticeSymm (s : Bool × Bool × Bool) (p : ℤ × ℤ) : ℤ × ℤ :=
  let q := if s.1 then (p.2, p.1) else p
  (if s.2.1 then -q.1 else q.1, if s.2.2 then -q.2 else q.2)

/-- The integer coordinates of a set of cells. -/
def coords {a b : ℕ} (S : Set (Fin a × Fin b)) : Set (ℤ × ℤ) :=
  (fun p => ((p.1 : ℤ), (p.2 : ℤ))) '' S

/-- Two sets of lattice points have the same shape: one is the image of the other under a
rotation or reflection of the lattice followed by a translation. -/
def SameShape (S T : Set (ℤ × ℤ)) : Prop :=
  ∃ s t, T = (fun p => latticeSymm s p + t) '' S

/-- The instance has a solution: a set `B` of black cells containing the initially black cells
and satisfying rules (1)-(5). -/
def ChainedBlockFeasible (i : ChainedBlockInstance) : Prop :=
  ∃ B : Set (Cell i), (∀ p, IsClue i p → p ∈ B) ∧
    -- (1) every block contains exactly one initially black cell (a number or `?`)
    (∀ c : Block i B, ∃! p, p ∈ blockCells c ∧ IsClue i p) ∧
    -- (2), (3) a number is the size of its block; `?` (stored as `0`) leaves the size free
    (∀ (c : Block i B) (p : Cell i), p ∈ blockCells c → IsClue i p → 0 < (entry i p).2 →
      (blockCells c).ncard = (entry i p).2) ∧
    -- (4) every block is part of a chain
    (∀ c : Block i B, ∃ d, Touch c d) ∧
    -- (5) different blocks in a single chain have different shapes
    ∀ c d : Block i B, c ≠ d → (chainGraph i B).Reachable c d →
      ¬ SameShape (coords (blockCells c)) (coords (blockCells d))

open Classical in
/-- CHAINED BLOCK as a decision problem over bitstrings. -/
noncomputable def chainedBlockDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChainedBlockInstance) x with
  | some i => decide (WellFormed i ∧ ChainedBlockFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainedBlock
