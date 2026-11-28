/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PIPE LINK: definitions

Source:
A. Uejima, H. Suzuki and A. Okada, "The Complexity of Generalized Pipe Link Puzzles",
Journal of Information Processing 25 (2017), 724-729, doi:10.2197/ipsjjip.25.724
(Section 1, rules (1)-(4), the Pipe Link Decision Problem and Theorem 1).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PipeLink

/-- An instance: the grid row by row, `0` for a blank square and `1`-`7` for a clue piece. -/
abbrev PipeLinkInstance := List (List ℕ)

/-- The number of rows. -/
def rows (i : PipeLinkInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : PipeLinkInstance) : ℕ := (i.headD []).length

/-- The entry of square `x`: `0` if blank, otherwise the code of its clue piece. -/
def piece (i : PipeLinkInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- The grid graph on the squares: orthogonally adjacent squares are adjacent. -/
abbrev Grid (i : PipeLinkInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, codes at most
`7`, and no clue piece has a line leaving the grid (rule 4): no upward line in the top row, no
downward line in the bottom row, no leftward line in the first column and no rightward line in
the last column. -/
def WellFormed (i : PipeLinkInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    (∀ row ∈ i, ∀ p ∈ row, p ≤ 7) ∧
    ∀ x : Fin (rows i) × Fin (cols i),
      ((x.1 : ℕ) = 0 → piece i x ∉ [2, 3, 6, 7]) ∧
      ((x.1 : ℕ) + 1 = rows i → piece i x ∉ [2, 4, 5, 7]) ∧
      ((x.2 : ℕ) = 0 → piece i x ∉ [1, 5, 6, 7]) ∧
      ((x.2 : ℕ) + 1 = cols i → piece i x ∉ [1, 3, 4, 7])

/-- The piece with code `p` in square `v` has a line on the side of `v` facing the square `w`
(up, down, left or right of `v`). -/
def OpensToward {m n : ℕ} (p : ℕ) (v w : Fin m × Fin n) : Prop :=
  ((w.1 : ℕ) + 1 = v.1 ∧ w.2 = v.2 ∧ p ∈ [2, 3, 6, 7]) ∨
    ((v.1 : ℕ) + 1 = w.1 ∧ w.2 = v.2 ∧ p ∈ [2, 4, 5, 7]) ∨
    (w.1 = v.1 ∧ (w.2 : ℕ) + 1 = v.2 ∧ p ∈ [1, 5, 6, 7]) ∨
    (w.1 = v.1 ∧ (v.2 : ℕ) + 1 = w.2 ∧ p ∈ [1, 3, 4, 7])

/-- The closed walk `c` is a loop solving the instance: rules 1-3. -/
def Solves (i : PipeLinkInstance) {u : Fin (rows i) × Fin (cols i)} (c : (Grid i).Walk u u) :
    Prop :=
  -- 1. a pipe is placed in every blank square, and the clue pieces lie on the loop
  (∀ x, x ∈ c.support) ∧
  -- 2. at a clue square the loop uses exactly the sides of the clue piece
  (∀ x w, piece i x ≠ 0 → (Grid i).Adj x w →
    (s(x, w) ∈ c.edges ↔ OpensToward (piece i x) x w)) ∧
  -- 3. where the loop turns (consecutive segments `d`, `d'`, cyclically), it passes only once;
  -- a square passed twice is an `X` pipe crossed by two straight lines
  ∀ dd ∈ c.darts.zip (c.darts.rotate 1),
    ¬ ((dd.1.fst.1 : ℕ) + (dd.2.snd.1 : ℕ) = 2 * (dd.1.snd.1 : ℕ) ∧
        (dd.1.fst.2 : ℕ) + (dd.2.snd.2 : ℕ) = 2 * (dd.1.snd.2 : ℕ)) →
      c.support.tail.count dd.1.snd ≤ 1

/-- Some closed loop of the grid graph, with no repeated segment, solves the instance. -/
def PipeLinkFeasible (i : PipeLinkInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCircuit ∧ Solves i c

open Classical in
/-- PIPE LINK as a decision problem over bitstrings. -/
noncomputable def pipeLinkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PipeLinkInstance) x with
  | some i => decide (WellFormed i ∧ PipeLinkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PipeLink
