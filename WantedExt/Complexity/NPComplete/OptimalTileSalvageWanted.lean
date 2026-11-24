/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL TILE SALVAGE (fixed x × y rectangles) is NP-complete

Source:
F. Berman, D. Johnson, T. Leighton, P. W. Shor and L. Snyder, "Generalized planar matching",
Journal of Algorithms 11 (1990), 153-184, doi:10.1016/0196-6774(90)90001-U (preprint: F. Berman,
T. Leighton, P. Shor and L. Snyder, "Generalized planar matching", MIT technical memorandum,
April 1985, https://hdl.handle.net/1721.1/149083; Sections 1 and 4, Figures 30-33).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Set.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalTileSalvage

/-!
# OPTIMAL TILE SALVAGE (fixed x × y rectangles) is NP-complete

Fix integers `1 ≤ x ≤ y` with `(x, y) ≠ (1, 1), (1, 2)`. INSTANCE: a finite region `R` of unit
cells of the integer grid (a rectilinear polygon made of grid cells, holes allowed) and a
positive integer `K`. QUESTION: can `K` pairwise non-overlapping `x × y` rectangles of cells, in
either orientation, be placed inside `R`?

Berman, Leighton, Shor and Snyder (Section 4): "Consider a `√N × √N` region of the plane tiled
with unit squares, some of which have been removed. The tiles which remain represent functional
chips and the tiles which have been removed represent faulty chips on a wafer. The optimal
`x, y` tile salvage problem is to find the maximum number of functional, non-overlapping `x × y`
tiled rectangles. The orientation of the rectangles does not matter and we assume without loss
of generality that `x ≤ y`. For `x = 1` and `y = 1`, the problem is trivial. For `x = 1` and
`y = 2`, the problem can easily be solved as an instance of the usual maximum matching problem.
... all but the trivial cases (`1 × 1`) and (`1 × 2`) are easily shown to be NP-complete."
(Section 1: "the `x × y` optimal tile salvage problem is NP-complete for all `{x, y}` except
`{1, 1}` and `{1, 2}`".) The decision version asks for at least `K` rectangles.

The region is the list of its cells `(a, b) ∈ ℕ × ℕ`, the cell `[a, a + 1] × [b, b + 1]`; any
square grid with removed cells is such a list, and any finite list fits in a square grid. A
rectangle is placed on the grid with its lower-left cell at `c` and is `w` cells wide and `h`
cells high, `(w, h) = (x, y)` or `(y, x)`; its cells are `Set.Ico c.1 (c.1 + w) ×ˢ
Set.Ico c.2 (c.2 + h)`. Rectangles must consist of cells of the region ("functional ... tiled
rectangles") and two rectangles may not share a cell ("non-overlapping"). Since the region is
given by its cells, the input size bounds its area.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the list of cells of the region and the bound `K`. -/
abbrev OptimalTileSalvageInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the cells are listed without repetition and `K > 0`. -/
def WellFormed (i : OptimalTileSalvageInstance) : Prop :=
  i.1.Nodup ∧ 0 < i.2

/-- The cells of the rectangle `w` cells wide and `h` cells high whose lower-left cell is `c`. -/
def rectCells (w h : ℕ) (c : ℕ × ℕ) : Set (ℕ × ℕ) :=
  Set.Ico c.1 (c.1 + w) ×ˢ Set.Ico c.2 (c.2 + h)

/-- The cells of the `x × y` rectangle placed at `p = (c, o)`: lower-left cell `c`, `x` wide and
`y` high if `o`, `y` wide and `x` high otherwise. -/
def placedCells (x y : ℕ) (p : (ℕ × ℕ) × Bool) : Set (ℕ × ℕ) :=
  if p.2 then rectCells x y p.1 else rectCells y x p.1

/-- `K` pairwise non-overlapping `x × y` rectangles, in either orientation, fit in the region. -/
def OptimalTileSalvageFeasible (x y : ℕ) (i : OptimalTileSalvageInstance) : Prop :=
  ∃ p : Fin i.2 → (ℕ × ℕ) × Bool, (∀ j, ∀ r ∈ placedCells x y (p j), r ∈ i.1) ∧
    ∀ j j', j ≠ j' → Disjoint (placedCells x y (p j)) (placedCells x y (p j'))

open Classical in
/-- OPTIMAL TILE SALVAGE with `x × y` rectangles as a decision problem over bitstrings. -/
noncomputable def optimalTileSalvageDec (x y : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun s =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OptimalTileSalvageInstance) s with
  | some i => decide (WellFormed i ∧ OptimalTileSalvageFeasible x y i)
  | none => false

/-- **OPTIMAL TILE SALVAGE is NP-complete for every fixed `x × y` rectangle other than `1 × 1`
and `1 × 2`.** Source: Berman, Johnson, Leighton, Shor and Snyder (1990), Section 4. -/
public theorem_wanted optimalTileSalvage_npComplete (x y : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y)
    (hne : (x, y) ≠ (1, 1) ∧ (x, y) ≠ (1, 2)) :
    optimalTileSalvageDec x y ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (optimalTileSalvageDec x y)

end MetaMathlibExt.Complexity.NPComplete.OptimalTileSalvage
