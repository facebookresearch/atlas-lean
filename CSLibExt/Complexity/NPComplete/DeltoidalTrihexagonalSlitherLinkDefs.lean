/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DELTOIDAL TRIHEXAGONAL SLITHER LINK: definitions

Source:
J. Kölker, "Selected Slither Link variants are NP-complete", Journal of Information
Processing 20(3) (2012), 709-712, doi:10.2197/ipsjjip.20.709, Theorem 4.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeltoidalTrihexagonalSlitherLink

/-- An instance: the clue grid, row by row from the top; entry `c` of row `r` lists the clues
of kites `0, …, 5` of hexagon `(c, r)`, `0` for no clue and `v + 1` for clue value `v`. -/
abbrev DeltoidalTrihexagonalSlitherLinkInstance := List (List (List ℕ))

/-- The number of rows `h`. -/
def height (i : DeltoidalTrihexagonalSlitherLinkInstance) : ℕ := i.length

/-- The number `w` of hexagons in each row (the length of the first row). -/
def width (i : DeltoidalTrihexagonalSlitherLinkInstance) : ℕ := (i.headD []).length

/-- The clue entry of kite `k` of hexagon `(c, r)`. -/
def clue (i : DeltoidalTrihexagonalSlitherLinkInstance) (c r k : ℕ) : ℕ :=
  ((i.getD r []).getD c []).getD k 0

/-- The six kites of hexagon `(c, r)`, each as its list of four sides; kite `k` is the kite at
the corner `Pₖ`, with center `Z` and side midpoints `Mₖ₋₁` and `Mₖ`. -/
def kites (c r : ℕ) : List (List (Sym2 (ℕ × ℕ))) :=
  let x := 2 * (2 * c + r % 2)
  let y := 2 * r
  let P₀ := (x, y)
  let P₁ := (x + 2, y)
  let P₂ := (x + 4, y)
  let P₃ := (x + 4, y + 2)
  let P₄ := (x + 2, y + 2)
  let P₅ := (x, y + 2)
  let M₀ := (x + 1, y)
  let M₁ := (x + 3, y)
  let M₂ := (x + 4, y + 1)
  let M₃ := (x + 3, y + 2)
  let M₄ := (x + 1, y + 2)
  let M₅ := (x, y + 1)
  let Z := (x + 2, y + 1)
  [[s(Z, M₅), s(M₅, P₀), s(P₀, M₀), s(M₀, Z)],
    [s(Z, M₀), s(M₀, P₁), s(P₁, M₁), s(M₁, Z)],
    [s(Z, M₁), s(M₁, P₂), s(P₂, M₂), s(M₂, Z)],
    [s(Z, M₂), s(M₂, P₃), s(P₃, M₃), s(M₃, Z)],
    [s(Z, M₃), s(M₃, P₄), s(P₄, M₄), s(M₄, Z)],
    [s(Z, M₄), s(M₄, P₅), s(P₅, M₅), s(M₅, Z)]]

/-- The four sides of kite `k` of hexagon `(c, r)`. -/
def kiteSides (c r k : ℕ) : List (Sym2 (ℕ × ℕ)) := (kites c r).getD k []

/-- The deltoidal trihexagonal grid with `h` rows of `w` hexagons: two points are adjacent when
they are the ends of a side of a kite of one of its hexagons. -/
def Graph (i : DeltoidalTrihexagonalSlitherLinkInstance) : SimpleGraph (ℕ × ℕ) :=
  SimpleGraph.fromRel fun p q =>
    ∃ c < width i, ∃ r < height i, ∃ k < 6, s(p, q) ∈ kiteSides c r k

/-- Well-formedness: `h ≥ 1` rows of `w ≥ 1` hexagons, each with `6` kite clue entries. -/
def WellFormed (i : DeltoidalTrihexagonalSlitherLinkInstance) : Prop :=
  0 < height i ∧ 0 < width i ∧ (∀ row ∈ i, row.length = width i) ∧
    ∀ row ∈ i, ∀ hex ∈ row, hex.length = 6

/-- Some cycle `cyc` of the grid has, for every clue kite, exactly as many of the kite's sides
among its edges as the clue value. -/
def DeltoidalTrihexagonalSlitherLinkFeasible (i : DeltoidalTrihexagonalSlitherLinkInstance) :
    Prop :=
  ∃ u, ∃ cyc : (Graph i).Walk u u, cyc.IsCycle ∧
    ∀ r < height i, ∀ c < width i, ∀ k < 6, 0 < clue i c r k →
      (kiteSides c r k).countP (· ∈ cyc.edges) + 1 = clue i c r k

open Classical in
/-- DELTOIDAL TRIHEXAGONAL SLITHER LINK as a decision problem over bitstrings. -/
noncomputable def deltoidalTrihexagonalSlitherLinkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DeltoidalTrihexagonalSlitherLinkInstance) x with
  | some i => decide (WellFormed i ∧ DeltoidalTrihexagonalSlitherLinkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DeltoidalTrihexagonalSlitherLink
