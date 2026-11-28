/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRIANGULAR SLITHER LINK: definitions

Source:
J. Kölker, "Selected Slither Link variants are NP-complete", Journal of Information
Processing 20(3) (2012), 709-712, doi:10.2197/ipsjjip.20.709, Theorem 2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangularSlitherLink

/-- An instance: the clue grid, row by row from the top; entry `k` of row `y` is the clue of
triangle `k` of row `y`, `0` for no clue and `v + 1` for clue value `v`. -/
abbrev TriangularSlitherLinkInstance := List (List ℕ)

/-- The number of rows `h`. -/
def height (i : TriangularSlitherLinkInstance) : ℕ := i.length

/-- The row length `w` (half the number of triangles in the first row). -/
def width (i : TriangularSlitherLinkInstance) : ℕ := (i.headD []).length / 2

/-- The clue entry of triangle `k` of row `y`. -/
def clue (i : TriangularSlitherLinkInstance) (y k : ℕ) : ℕ := (i.getD y []).getD k 0

/-- The edge relation of the unbounded triangular grid, from `p` to a point `q` to its right
on the same line or on the next line. -/
def GridEdge (p q : ℕ × ℕ) : Prop :=
  (q.2 = p.2 ∧ q.1 = p.1 + 1) ∨
    (q.2 = p.2 + 1 ∧ (q.1 = p.1 ∨ if p.2 % 2 = 0 then p.1 = q.1 + 1 else q.1 = p.1 + 1))

/-- The triangular grid with `h` rows of length `w`, on vertices `(x, y)`, `x ≤ w`, `y ≤ h`. -/
def Graph (i : TriangularSlitherLinkInstance) : SimpleGraph (ℕ × ℕ) :=
  SimpleGraph.fromRel fun p q =>
    p.1 ≤ width i ∧ p.2 ≤ height i ∧ q.1 ≤ width i ∧ q.2 ≤ height i ∧ GridEdge p q

/-- The three corners of triangle `k` of row `y`, with `a = k / 2`: a down triangle has
corners `(a, y)`, `(a + 1, y)` and `(a + y % 2, y + 1)`; an up triangle has corners
`(a, y + 1)`, `(a + 1, y + 1)` and `(a + 1 - y % 2, y)`. -/
def corners (y k : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) :=
  if (y + k) % 2 = 0 then ((k / 2, y), (k / 2 + 1, y), (k / 2 + y % 2, y + 1))
  else ((k / 2, y + 1), (k / 2 + 1, y + 1), (k / 2 + 1 - y % 2, y))

/-- The three sides of triangle `k` of row `y`. -/
def sides (y k : ℕ) : List (Sym2 (ℕ × ℕ)) :=
  let t := corners y k
  [s(t.1, t.2.1), s(t.2.1, t.2.2), s(t.1, t.2.2)]

/-- Well-formedness: `h > 1` rows (as in Section 5), every row of the same positive even length
`2w`. -/
def WellFormed (i : TriangularSlitherLinkInstance) : Prop :=
  1 < height i ∧ 0 < width i ∧ ∀ row ∈ i, row.length = 2 * width i

/-- Some cycle `c` of the grid has, for every clue triangle, exactly as many of the triangle's
sides among its edges as the clue value. -/
def TriangularSlitherLinkFeasible (i : TriangularSlitherLinkInstance) : Prop :=
  ∃ u, ∃ c : (Graph i).Walk u u, c.IsCycle ∧
    ∀ y < height i, ∀ k < 2 * width i, 0 < clue i y k →
      (sides y k).countP (· ∈ c.edges) + 1 = clue i y k

open Classical in
/-- TRIANGULAR SLITHER LINK as a decision problem over bitstrings. -/
noncomputable def triangularSlitherLinkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangularSlitherLinkInstance) x with
  | some i => decide (WellFormed i ∧ TriangularSlitherLinkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TriangularSlitherLink
