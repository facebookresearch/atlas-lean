/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL TILE SALVAGE (fixed x × y rectangles): definitions

Source:
F. Berman, D. Johnson, T. Leighton, P. W. Shor and L. Snyder, "Generalized planar matching",
Journal of Algorithms 11 (1990), 153-184, doi:10.1016/0196-6774(90)90001-U (preprint: F. Berman,
T. Leighton, P. Shor and L. Snyder, "Generalized planar matching", MIT technical memorandum,
April 1985, https://hdl.handle.net/1721.1/149083; Sections 1 and 4, Figures 30-33).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Set.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalTileSalvage

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

end MetaMathlibExt.Complexity.NPComplete.OptimalTileSalvage
