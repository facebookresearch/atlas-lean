/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CORRAL (BAG) is NP-complete

Source:
E. Friedman, "Corral puzzles are NP-complete", manuscript, Stetson University (2002),
https://erich-friedman.github.io/papers/corral.pdf.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Corral

/-!
# CORRAL (BAG) is NP-complete

Friedman (2002): "Each puzzle consists of a grid of squares, some of which contain numbers. The
goal is to find a closed loop containing some of the grid squares so that all the numbers are
inside the loop and each number is equal to the number of grid squares visible from it. A grid
square is visible from a number if it is horizontally or vertically aligned with it and all the
squares between them are inside the loop." The loop runs along the grid lines (Nikoli's Bag:
"a single, continuous loop along the lines of the grid"), and a visible square is itself inside
the loop, the numbered square included (Nikoli: the cells visible "before a line of the loop is
reached, plus the cell itself"). Friedman proves that deciding whether a Corral puzzle has a
solution is NP-complete, by a reduction from 3-coloring of planar graphs.

INSTANCE: an `m × n` grid of squares, some of which contain positive integers.
QUESTION: is there a closed loop along the grid lines such that every numbered square is inside
the loop and sees exactly its number of squares inside the loop (itself included) along its row
and column, without an outside square in between?

Representation. The grid is given row by row: entry `c` of row `r` is `0` for an empty square
and `k ≥ 1` for a square containing `k`, so the instance size is proportional to the area of
the grid plus the binary length of the numbers. The grid lines form Mathlib's grid graph
`pathGraph (m + 1) □ pathGraph (n + 1)` on the corner points `(r, c)`, `r ≤ m`, `c ≤ n`;
square `(r, c)` has corners `(r, c)`, `(r, c + 1)`, `(r + 1, c)` and `(r + 1, c + 1)`. A
closed loop along the grid lines is a cycle of this graph (`SimpleGraph.Walk.IsCycle`); it
does not cross or touch itself. A square is inside the loop when the horizontal ray from its
center to the right crosses the loop an odd number of times (the even-odd rule, which for a
simple closed polygon picks out its interior); the ray from the center of square `(r, c)`
crosses exactly the vertical unit segments `(r, d)`-`(r + 1, d)` with `c < d`. A square `y`
in the row or column of the numbered square `x` is visible from `x` when every square from `x`
to `y` (both included) is inside the loop.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the grid row by row, `0` for an empty square and `k ≥ 1` for a square
containing `k`. -/
abbrev CorralInstance := List (List ℕ)

/-- The number of rows `m`. -/
def rows (i : CorralInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
def cols (i : CorralInstance) : ℕ := (i.headD []).length

/-- The number in square `(r, c)` (`0` if empty). -/
def number (i : CorralInstance) (r c : ℕ) : ℕ := (i.getD r []).getD c 0

/-- The grid lines: the grid graph on the corner points `(r, c)`, `r ≤ m`, `c ≤ n`. -/
abbrev Lines (i : CorralInstance) : SimpleGraph (Fin (rows i + 1) × Fin (cols i + 1)) :=
  SimpleGraph.pathGraph (rows i + 1) □ SimpleGraph.pathGraph (cols i + 1)

/-- The unit segments of a walk along the grid lines, with corner points as pairs of
naturals. -/
def segments (i : CorralInstance) {u v : Fin (rows i + 1) × Fin (cols i + 1)}
    (w : (Lines i).Walk u v) : List (Sym2 (ℕ × ℕ)) :=
  w.edges.map (Sym2.map fun p => ((p.1 : ℕ), (p.2 : ℕ)))

/-- Square `(r, c)` is inside the loop `l`: the ray from its center to the right crosses an odd
number of the loop's vertical unit segments `(r, d)`-`(r + 1, d)`, `c < d`. -/
def Inside (i : CorralInstance) {u : Fin (rows i + 1) × Fin (cols i + 1)}
    (l : (Lines i).Walk u u) (r c : ℕ) : Prop :=
  ((List.range (cols i + 1)).filter fun d =>
    c < d ∧ s((r, d), (r + 1, d)) ∈ segments i l).length % 2 = 1

instance (i : CorralInstance) {u : Fin (rows i + 1) × Fin (cols i + 1)}
    (l : (Lines i).Walk u u) (r c : ℕ) : Decidable (Inside i l r c) :=
  inferInstanceAs (Decidable (_ % 2 = 1))

/-- The number of squares visible from square `(r, c)`: the square itself, plus the other
squares `(r, d)` of its row and `(e, c)` of its column such that every square between them and
`(r, c)`, both included, is inside the loop `l`. -/
def visible (i : CorralInstance) {u : Fin (rows i + 1) × Fin (cols i + 1)}
    (l : (Lines i).Walk u u) (r c : ℕ) : ℕ :=
  1 + ((List.range (cols i)).filter fun d =>
      d ≠ c ∧ ∀ t < cols i, min c d ≤ t → t ≤ max c d → Inside i l r t).length +
    ((List.range (rows i)).filter fun e =>
      e ≠ r ∧ ∀ t < rows i, min r e ≤ t → t ≤ max r e → Inside i l t c).length

/-- Well-formedness: the grid has at least one row and one column, and rows of equal
length. -/
def WellFormed (i : CorralInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ ∀ row ∈ i, row.length = cols i

/-- Some loop along the grid lines has every numbered square inside it and seeing exactly its
number of squares. -/
def CorralFeasible (i : CorralInstance) : Prop :=
  ∃ u : Fin (rows i + 1) × Fin (cols i + 1), ∃ l : (Lines i).Walk u u, l.IsCycle ∧
    ∀ r < rows i, ∀ c < cols i, 0 < number i r c →
      Inside i l r c ∧ visible i l r c = number i r c

open Classical in
/-- CORRAL (BAG) as a decision problem over bitstrings. -/
noncomputable def corralDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CorralInstance) x with
  | some i => decide (WellFormed i ∧ CorralFeasible i)
  | none => false

/-- **CORRAL (BAG) is NP-complete.** Source: Friedman (2002). -/
public theorem_wanted corral_npComplete :
    corralDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L corralDec

end MetaMathlibExt.Complexity.NPComplete.Corral
