/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TILEPAINT is NP-complete

Source:
C. Iwamoto and T. Ide, "Five Cells and Tilepaint are NP-complete", IEICE Transactions on
Information and Systems E105-D(3) (2022), 508-516, doi:10.1587/transinf.2021FCP0001,
Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Tilepaint

/-!
# TILEPAINT is NP-complete

INSTANCE: a rectangular grid of cells divided into tiles, the areas enclosed by bold lines, and
a number assigned to each row and each column.
QUESTION: can cells be painted black so that (i) the number of each row (resp. each column) is
the number of black cells in the row (resp. column), and (ii) the cells of each tile are all
black or all left uncolored?

A tile is a set of cells connected through orthogonally adjacent cells of the same tile. The
grid with `h` rows and `w` columns is Mathlib's grid graph `pathGraph h □ pathGraph w` on
`Fin h × Fin w`; keeping only its edges inside tiles gives `tileGraph`.

The instance lists the rows of the grid, top to bottom, each entry the name (a natural number)
of the tile containing the cell, followed by the row numbers, top to bottom, and the column
numbers, left to right.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the grid rows (top to bottom) of tile names, the row numbers (top to bottom)
and the column numbers (left to right). -/
abbrev TilepaintInstance := List (List ℕ) × List ℕ × List ℕ

/-- The number of rows. -/
abbrev rows (i : TilepaintInstance) : ℕ := i.1.length

/-- The number of columns, the length of the first row. -/
abbrev cols (i : TilepaintInstance) : ℕ := (i.1.headD []).length

/-- The tile containing the cell in row `p.1` and column `p.2`. -/
def tile (i : TilepaintInstance) (p : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.1.getD p.1 []).getD p.2 0

/-- The number assigned to row `r`. -/
def rowNumber (i : TilepaintInstance) (r : Fin (rows i)) : ℕ :=
  i.2.1.getD r 0

/-- The number assigned to column `c`. -/
def colNumber (i : TilepaintInstance) (c : Fin (cols i)) : ℕ :=
  i.2.2.getD c 0

/-- The grid graph: cells are adjacent when they share a side. -/
abbrev grid (h w : ℕ) : SimpleGraph (Fin h × Fin w) :=
  SimpleGraph.pathGraph h □ SimpleGraph.pathGraph w

/-- The grid edges between cells of the same tile. -/
def tileGraph (i : TilepaintInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  grid (rows i) (cols i) ⊓ SimpleGraph.fromRel fun p q => tile i p = tile i q

/-- Well-formedness of an instance: the grid has at least one row and one column, every row has
the same length, each row and each column has a number, and every tile is connected. -/
def WellFormed (i : TilepaintInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.1, row.length = cols i) ∧
    i.2.1.length = rows i ∧ i.2.2.length = cols i ∧
    ∀ p q, tile i p = tile i q → (tileGraph i).Reachable p q

/-- Some painting satisfies the rules: each tile is all black or all uncolored, and every row and
every column has as many black cells as its number. -/
def TilepaintFeasible (i : TilepaintInstance) : Prop :=
  ∃ black : Fin (rows i) × Fin (cols i) → Bool,
    (∀ p q, tile i p = tile i q → black p = black q) ∧
    (∀ r, (Finset.univ.filter fun c => black (r, c) = true).card = rowNumber i r) ∧
    ∀ c, (Finset.univ.filter fun r => black (r, c) = true).card = colNumber i c

open Classical in
/-- TILEPAINT as a decision problem over bitstrings. -/
noncomputable def tilepaintDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TilepaintInstance) x with
  | some i => decide (WellFormed i ∧ TilepaintFeasible i)
  | none => false

/-- **TILEPAINT is NP-complete.** Source: Iwamoto and Ide (2022), Theorem 1. -/
public theorem_wanted tilepaint_npComplete :
    tilepaintDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tilepaintDec

end MetaMathlibExt.Complexity.NPComplete.Tilepaint
