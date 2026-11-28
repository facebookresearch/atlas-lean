/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOSUN-FUWARI is NP-complete

Source:
C. Iwamoto and T. Ibusuki, "Dosun-Fuwari is NP-complete", Journal of Information Processing 26
(2018), 358-361, doi:10.2197/ipsjjip.26.358.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DosunFuwari

/-!
# DOSUN-FUWARI is NP-complete

INSTANCE: a rectangular grid of cells, partitioned into black cells and rooms.
QUESTION: can balloons and iron balls be placed in the cells of the rooms so that
(1) each room contains exactly one balloon and exactly one iron ball,
(2) every balloon is in the top row of the grid, or in a cell right under a black cell or right
under another balloon, and
(3) every iron ball is in the bottom row of the grid, or in a cell right over a black cell or
right over another iron ball?

A cell holds at most one object, and black cells hold none. A room is a region of the grid
surrounded by bold lines: a set of cells connected through orthogonally adjacent cells of the
same room. The grid with `h` rows and `w` columns is Mathlib's grid graph
`pathGraph h □ pathGraph w` on `Fin h × Fin w`; keeping only its edges inside rooms gives
`roomGraph`.

The instance lists the rows of the grid, top to bottom (row `0` is the top row); entry `0` is a
black cell and an entry `k ≥ 1` is a cell of room `k`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the rows of the grid, top to bottom; entry `0` is a black cell and an entry
`k ≥ 1` a cell of room `k`. -/
abbrev DosunFuwariInstance := List (List ℕ)

/-- The number of rows. -/
abbrev rows (i : DosunFuwariInstance) : ℕ := i.length

/-- The number of columns, the length of the first row. -/
abbrev cols (i : DosunFuwariInstance) : ℕ := (i.headD []).length

/-- The entry of the cell in row `p.1` and column `p.2`: `0` for a black cell, `k` for a cell of
room `k`. -/
def label (i : DosunFuwariInstance) (p : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.getD p.1 []).getD p.2 0

/-- The grid graph: cells are adjacent when they share a side. -/
abbrev grid (h w : ℕ) : SimpleGraph (Fin h × Fin w) :=
  SimpleGraph.pathGraph h □ SimpleGraph.pathGraph w

/-- The grid edges between cells with the same entry, `0` included; its components are maximal
connected same-label sets. Feasibility counts objects per positive label; only for well-formed
grids, where each label's cells are mutually reachable, are the positive components the rooms. -/
def roomGraph (i : DosunFuwariInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  grid (rows i) (cols i) ⊓ SimpleGraph.fromRel fun p q => label i p = label i q

/-- Well-formedness of an instance: the grid has at least one row and one column, every row has
the same length, and every room is connected. -/
def WellFormed (i : DosunFuwariInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ p q, label i p ≠ 0 → label i p = label i q → (roomGraph i).Reachable p q

/-- Some placement of balloons and iron balls satisfies the rules: objects sit in distinct room
cells, each room holds exactly one balloon and exactly one iron ball, every balloon is in the top
row or right under a black cell or a balloon, and every iron ball is in the bottom row or right
over a black cell or an iron ball. -/
def DosunFuwariFeasible (i : DosunFuwariInstance) : Prop :=
  ∃ balloons irons : Finset (Fin (rows i) × Fin (cols i)),
    Disjoint balloons irons ∧
    (∀ p ∈ balloons, label i p ≠ 0) ∧ (∀ p ∈ irons, label i p ≠ 0) ∧
    (∀ p, label i p ≠ 0 →
      (balloons.filter fun q => label i q = label i p).card = 1 ∧
      (irons.filter fun q => label i q = label i p).card = 1) ∧
    (∀ p ∈ balloons, (p.1 : ℕ) = 0 ∨
      ∃ q : Fin (rows i) × Fin (cols i), (q.1 : ℕ) + 1 = p.1 ∧ q.2 = p.2 ∧
        (label i q = 0 ∨ q ∈ balloons)) ∧
    ∀ p ∈ irons, (p.1 : ℕ) + 1 = rows i ∨
      ∃ q : Fin (rows i) × Fin (cols i), (p.1 : ℕ) + 1 = q.1 ∧ q.2 = p.2 ∧
        (label i q = 0 ∨ q ∈ irons)

open Classical in
/-- DOSUN-FUWARI as a decision problem over bitstrings. -/
noncomputable def dosunFuwariDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DosunFuwariInstance) x with
  | some i => decide (WellFormed i ∧ DosunFuwariFeasible i)
  | none => false

/-- **DOSUN-FUWARI is NP-complete.** Source: Iwamoto and Ibusuki (2018). -/
public theorem_wanted dosunFuwari_npComplete :
    dosunFuwariDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dosunFuwariDec

end MetaMathlibExt.Complexity.NPComplete.DosunFuwari
