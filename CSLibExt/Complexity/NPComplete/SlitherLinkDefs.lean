/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SLITHER LINK: definitions

Source:
T. Yato, "On the NP-completeness of the Slither Link puzzle", IPSJ SIG Notes AL-74 (2000),
25-32;
T. Yato and T. Seta, "Complexity and completeness of finding another solution and its
application to puzzles", IEICE Transactions on Fundamentals of Electronics, Communications and
Computer Sciences E86-A(5) (2003), 1052-1060;
T. Yato, "Complexity and completeness of finding another solution and its application to
puzzles", Master's thesis, University of Tokyo (2003), Section 3.1, Theorem 3.3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SlitherLink

/-- An instance: the cells row by row; entry `k` of row `r` is `0` when cell `(r, k)` has no
number and `v + 1` when it carries the number `v`. -/
abbrev SlitherLinkInstance := List (List ℕ)

/-- The number of rows of cells `m`. -/
abbrev rows (i : SlitherLinkInstance) : ℕ := i.length

/-- The number of columns of cells `n` (the length of the first row). -/
abbrev cols (i : SlitherLinkInstance) : ℕ := (i.headD []).length

/-- A lattice point `(row, column)` of the `m × n` lattice. -/
abbrev Point (i : SlitherLinkInstance) := Fin (rows i + 1) × Fin (cols i + 1)

/-- The lattice graph: lattice points at distance one are adjacent. -/
abbrev Lattice (i : SlitherLinkInstance) : SimpleGraph (Point i) :=
  SimpleGraph.pathGraph (rows i + 1) □ SimpleGraph.pathGraph (cols i + 1)

/-- The entry of cell `(r, k)`: `0` for no number, `v + 1` for the number `v`. -/
def clue (i : SlitherLinkInstance) (r : Fin (rows i)) (k : Fin (cols i)) : ℕ :=
  (i.getD r []).getD k 0

/-- The four sides of cell `(r, k)`: top, bottom, left and right. -/
def sides (i : SlitherLinkInstance) (r : Fin (rows i)) (k : Fin (cols i)) :
    List (Sym2 (Point i)) :=
  [s((r.castSucc, k.castSucc), (r.castSucc, k.succ)),
    s((r.succ, k.castSucc), (r.succ, k.succ)),
    s((r.castSucc, k.castSucc), (r.succ, k.castSucc)),
    s((r.castSucc, k.succ), (r.succ, k.succ))]

/-- Well-formedness: at least one row and one column, rows of equal length, and every entry at
most `4` (numbers `0` to `3`). -/
def WellFormed (i : SlitherLinkInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧ ∀ row ∈ i, ∀ e ∈ row, e ≤ 4

/-- Some cycle `c` of the lattice graph has, for every numbered cell, exactly as many of the
cell's four sides among its edges as the cell's number. -/
def SlitherLinkFeasible (i : SlitherLinkInstance) : Prop :=
  ∃ u, ∃ c : (Lattice i).Walk u u, c.IsCycle ∧
    ∀ r k, clue i r k ≠ 0 → (sides i r k).countP (· ∈ c.edges) + 1 = clue i r k

open Classical in
/-- SLITHER LINK as a decision problem over bitstrings. -/
noncomputable def slitherLinkDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := SlitherLinkInstance) x with
  | some i => decide (WellFormed i ∧ SlitherLinkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SlitherLink
