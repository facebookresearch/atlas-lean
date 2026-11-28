/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZIG-ZAG NUMBERLINK: definitions

Source:
A. Adcock, E. D. Demaine, M. L. Demaine, M. P. O'Brien, F. Reidl, F. Sánchez Villaamil, and
B. D. Sullivan, "Zig-zag Numberlink is NP-complete", Journal of Information Processing 23(3)
(2015), 239-245, doi:10.2197/ipsjjip.23.239 (arXiv:1410.5845, Definitions 1-4 and Theorem 1).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ZigZagNumberlink

/-- An instance: the board row by row; each square is `0` (no terminal) or `c ≥ 1` (a terminal
of pair `c`). -/
abbrev ZigZagNumberlinkInstance := List (List ℕ)

/-- The number of rows `m`. -/
abbrev rows (i : ZigZagNumberlinkInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
abbrev cols (i : ZigZagNumberlinkInstance) : ℕ := (i.headD []).length

/-- The grid graph of the board: squares `(r, c)`, adjacent when they share a side. -/
abbrev Grid (i : ZigZagNumberlinkInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The content of square `(r, c)`: `0`, or the pair `c ≥ 1` of the terminal on it. -/
def square (i : ZigZagNumberlinkInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- Well-formedness of an instance: the board has at least one row and one column, all rows have
the same length (the board is rectangular), and every pair label that occurs is on exactly two
squares (a terminal pair of distinct squares; terminals are distinct since a square holds one
label). -/
def WellFormed (i : ZigZagNumberlinkInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ c ∈ i.flatten, 0 < c → i.flatten.count c = 2

/-- Paths connect every terminal pair and cover every square exactly once: every square is owned
by a pair that occurs on the board, and for each pair `c` with terminals `s ≠ t` some path from `s`
to `t` passes exactly through the squares owned by `c`. -/
def ZigZagNumberlinkFeasible (i : ZigZagNumberlinkInstance) : Prop :=
  ∃ owner : Fin (rows i) × Fin (cols i) → ℕ,
    (∀ x, ∃ s, 0 < square i s ∧ square i s = owner x) ∧
    ∀ s t, 0 < square i s → square i t = square i s → s ≠ t →
      ∃ p : (Grid i).Walk s t, p.IsPath ∧ ∀ x, x ∈ p.support ↔ owner x = square i s

open Classical in
/-- ZIG-ZAG NUMBERLINK as a decision problem over bitstrings. -/
noncomputable def zigZagNumberlinkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ZigZagNumberlinkInstance) x with
  | some i => decide (WellFormed i ∧ ZigZagNumberlinkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ZigZagNumberlink
