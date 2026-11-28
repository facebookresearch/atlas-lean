/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRUNCATED HEXAGONAL SLITHER LINK: definitions

Source:
J. Kölker, "Selected Slither Link variants are NP-complete", Journal of Information
Processing 20(3) (2012), 709-712, doi:10.2197/ipsjjip.20.709, Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TruncatedHexagonalSlitherLink

/-- An instance: the dodecagon clue grid (row `r`, entry `c` for dodecagon `(c, r)`) and the
triangle clue grid (row `y`, entry `x` for the triangle at hex vertex `(x, y)`); `0` for no
clue and `v + 1` for clue value `v`. -/
abbrev TruncatedHexagonalSlitherLinkInstance := List (List ℕ) × List (List ℕ)

/-- A vertex of the truncated grid: the pair `(p, q)` is the vertex on the hex side from `p` to
`q` next to `p`. -/
abbrev Point := (ℕ × ℕ) × (ℕ × ℕ)

/-- The number of rows `h`. -/
def height (i : TruncatedHexagonalSlitherLinkInstance) : ℕ := i.1.length

/-- The number `w` of dodecagons in each row (the length of the first row). -/
def width (i : TruncatedHexagonalSlitherLinkInstance) : ℕ := (i.1.headD []).length

/-- The clue entry of dodecagon `(c, r)`. -/
def dodecagonClue (i : TruncatedHexagonalSlitherLinkInstance) (c r : ℕ) : ℕ :=
  (i.1.getD r []).getD c 0

/-- The clue entry of the triangle at hex vertex `(x, y)`. -/
def triangleClue (i : TruncatedHexagonalSlitherLinkInstance) (x y : ℕ) : ℕ :=
  (i.2.getD y []).getD x 0

/-- The twelve sides of dodecagon `(c, r)`, obtained from hexagon `(c, r)` with corners
`p₀, …, p₅`: for each `k`, the side cutting the corner `pₖ` and the rest of the hex side
`pₖpₖ₊₁`. -/
def dodecagonSides (c r : ℕ) : List (Sym2 Point) :=
  let x₀ := 2 * c + r % 2
  let p₀ := (x₀, r)
  let p₁ := (x₀ + 1, r)
  let p₂ := (x₀ + 2, r)
  let p₃ := (x₀ + 2, r + 1)
  let p₄ := (x₀ + 1, r + 1)
  let p₅ := (x₀, r + 1)
  [s((p₀, p₅), (p₀, p₁)), s((p₀, p₁), (p₁, p₀)),
    s((p₁, p₀), (p₁, p₂)), s((p₁, p₂), (p₂, p₁)),
    s((p₂, p₁), (p₂, p₃)), s((p₂, p₃), (p₃, p₂)),
    s((p₃, p₂), (p₃, p₄)), s((p₃, p₄), (p₄, p₃)),
    s((p₄, p₃), (p₄, p₅)), s((p₄, p₅), (p₅, p₄)),
    s((p₅, p₄), (p₅, p₀)), s((p₅, p₀), (p₀, p₅))]

/-- The three sides of the triangle at hex vertex `p = (x, y)`, whose hex neighbours are
`(x - 1, y)`, `(x + 1, y)` and `(x, y + 1)` or `(x, y - 1)` as `x + y` is even or odd. -/
def triangleSides (p : ℕ × ℕ) : List (Sym2 Point) :=
  let a := (p.1 - 1, p.2)
  let b := (p.1 + 1, p.2)
  let d := if (p.1 + p.2) % 2 = 0 then (p.1, p.2 + 1) else (p.1, p.2 - 1)
  [s((p, a), (p, b)), s((p, b), (p, d)), s((p, a), (p, d))]

/-- The truncated hexagonal grid with `h` rows of `w` dodecagons: two vertices are adjacent
when they are the ends of a side of one of its dodecagons. -/
def Graph (i : TruncatedHexagonalSlitherLinkInstance) : SimpleGraph Point :=
  SimpleGraph.fromRel fun u v => ∃ c < width i, ∃ r < height i, s(u, v) ∈ dodecagonSides c r

/-- Well-formedness: `h ≥ 1` rows of `w ≥ 1` dodecagon clue entries, `h + 1` rows of `2w + 2`
triangle clue entries, and clues only on triangles that are faces of the grid. -/
def WellFormed (i : TruncatedHexagonalSlitherLinkInstance) : Prop :=
  0 < height i ∧ 0 < width i ∧ (∀ row ∈ i.1, row.length = width i) ∧
    i.2.length = height i + 1 ∧ (∀ row ∈ i.2, row.length = 2 * width i + 2) ∧
    ∀ y ≤ height i, ∀ x ≤ 2 * width i + 1, 0 < triangleClue i x y →
      ∀ e ∈ triangleSides (x, y), e ∈ (Graph i).edgeSet

/-- Some cycle `cyc` of the grid has, for every clue dodecagon and every clue triangle, exactly
as many of the face's sides among its edges as the clue value. -/
def TruncatedHexagonalSlitherLinkFeasible (i : TruncatedHexagonalSlitherLinkInstance) : Prop :=
  ∃ u, ∃ cyc : (Graph i).Walk u u, cyc.IsCycle ∧
    (∀ r < height i, ∀ c < width i, 0 < dodecagonClue i c r →
      (dodecagonSides c r).countP (· ∈ cyc.edges) + 1 = dodecagonClue i c r) ∧
    ∀ y ≤ height i, ∀ x ≤ 2 * width i + 1, 0 < triangleClue i x y →
      (triangleSides (x, y)).countP (· ∈ cyc.edges) + 1 = triangleClue i x y

open Classical in
/-- TRUNCATED HEXAGONAL SLITHER LINK as a decision problem over bitstrings. -/
noncomputable def truncatedHexagonalSlitherLinkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TruncatedHexagonalSlitherLinkInstance) x with
  | some i => decide (WellFormed i ∧ TruncatedHexagonalSlitherLinkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TruncatedHexagonalSlitherLink
