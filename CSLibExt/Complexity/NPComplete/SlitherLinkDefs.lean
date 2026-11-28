/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# SLITHER LINK: definitions

Yato (2003, Section 3.1) states the rules of Slither Link:
* "Each problem is given as a rectangular lattice. The length of sides of the rectangle (as to
  the unit length of lattice) is called the size of the problem."
* "A 1 × 1 square surrounded by four points is called a cell. A cell may have a number out of
  0, 1, 2 or 3."
* "The goal is to make a loop which does not intersect or branch by connecting adjacent dots
  with lines, so that a number on the cell is equal to the number of lines drawn around it."

INSTANCE: an `m × n` rectangular lattice of cells (`m, n ≥ 1`), some cells carrying a number
in `{0, 1, 2, 3}`.
QUESTION: is there a loop along lattice lines, without crossings or branches, such that every
numbered cell has exactly that many of its four sides on the loop?

Yato (2000) proved this NP-complete. Yato and Seta (2003) and Yato (2003, Theorem 3.3) prove
that finding a solution is ASP-complete, and Yato (2003, Theorem 2.7, with `n = 0`) shows that
the decision problem of an ASP-complete problem is NP-complete.

Representation. The cells are given explicitly, row by row: entry `k` of row `r` is `0` when
cell `(r, k)` has no number and `v + 1` when it carries the number `v`, so the instance size is
proportional to the area of the lattice. `WellFormed` requires at least one row and one column,
rows of equal length and entries at most `4`. The lattice points of an `m × n` lattice are
`Fin (m + 1) × Fin (n + 1)` (row, column); adjacent dots, at distance one, are adjacent in
Mathlib's grid graph `pathGraph (m + 1) □ pathGraph (n + 1)`. Cell `(r, k)` is the square with
corners `(r, k)`, `(r, k + 1)`, `(r + 1, k)` and `(r + 1, k + 1)`, and its four sides are the
lattice edges between consecutive corners. A loop that does not intersect or branch is a cycle
`c` of the lattice graph (`SimpleGraph.Walk.IsCycle`), and the lines drawn are its edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
T. Yato, "On the NP-completeness of the Slither Link puzzle", IPSJ SIG Notes AL-74 (2000),
25-32;
T. Yato and T. Seta, "Complexity and completeness of finding another solution and its
application to puzzles", IEICE Transactions on Fundamentals of Electronics, Communications and
Computer Sciences E86-A(5) (2003), 1052-1060;
T. Yato, "Complexity and completeness of finding another solution and its application to
puzzles", Master's thesis, University of Tokyo (2003), Section 3.1, Theorem 3.3.
-/

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
