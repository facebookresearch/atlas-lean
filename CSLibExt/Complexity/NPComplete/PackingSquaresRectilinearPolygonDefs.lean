/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PACKING SQUARES IN A RECTILINEAR POLYGON: definitions

Source:
R. J. Fowler, M. S. Paterson and S. L. Tanimoto, "Optimal packing and covering in the plane are
NP-complete", Information Processing Letters 12 (1981), 133-137,
doi:10.1016/0020-0190(81)90111-3 (full text not available here; the result for `3 × 3` squares
as recorded by Berman et al.);
F. Berman, D. Johnson, T. Leighton, P. W. Shor and L. Snyder, "Generalized planar matching",
Journal of Algorithms 11 (1990), 153-184, doi:10.1016/0196-6774(90)90001-U (preprint: MIT
technical memorandum, April 1985, https://hdl.handle.net/1721.1/149083; Sections 1 and 4: the
optimal tile salvage problem, NP-complete for `x × y` rectangles other than `1 × 1` and `1 × 2`,
in particular for `d × d` squares with `d ≥ 2`, and "Fowler, Paterson and Tanimoto [5] proved
that finding the maximum number of `3 × 3` squares of functioning cells is NP-complete");
A. Aamand, M. Abrahamsen, T. D. Ahle and P. M. R. Rasmussen, "Tiling with squares and packing
dominos in polynomial time", ACM Transactions on Algorithms 19 (2023), 1-28,
doi:10.1145/3597932 (arXiv:2011.10983; Section 1: Fowler, Paterson and Tanimoto "showed ... that
deciding whether a given number of `3 × 3` squares can be packed into a polyomino (with holes) is
NP-complete, and the result was strengthened to `2 × 2` squares by Berman, Johnson, Leighton,
Shor, & Snyder", with the container given as the list of its cells).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Set.Prod
public import CSLibExt.Complexity.NPComplete.PolyominoPackingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PackingSquaresRectilinearPolygon

/-- An instance: the side `d` of the squares, the list of cells of the polygon, and the bound
`K`. -/
abbrev PackingSquaresRectilinearPolygonInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: `d > 0`, the cells are listed without repetition and form a
polyomino (a nonempty edge-connected cell set, `isPolycubeCells 2`), and `K > 0`. -/
def WellFormed (i : PackingSquaresRectilinearPolygonInstance) : Prop :=
  0 < i.1 ∧ i.2.1.Nodup ∧ isPolycubeCells 2 (PolyominoPacking.pieceCells i.2.1) ∧ 0 < i.2.2

/-- `K` pairwise disjoint `d × d` squares fit in the polygon: the square `j` has lower-left cell
`c j` and covers the cells `Set.Ico (c j).1 ((c j).1 + d) ×ˢ Set.Ico (c j).2 ((c j).2 + d)`. -/
def PackingSquaresRectilinearPolygonFeasible
    (i : PackingSquaresRectilinearPolygonInstance) : Prop :=
  ∃ c : Fin i.2.2 → ℕ × ℕ,
    (∀ j, ∀ r ∈ Set.Ico (c j).1 ((c j).1 + i.1) ×ˢ Set.Ico (c j).2 ((c j).2 + i.1), r ∈ i.2.1) ∧
    ∀ j j', j ≠ j' → Disjoint (Set.Ico (c j).1 ((c j).1 + i.1) ×ˢ Set.Ico (c j).2 ((c j).2 + i.1))
      (Set.Ico (c j').1 ((c j').1 + i.1) ×ˢ Set.Ico (c j').2 ((c j').2 + i.1))

open Classical in
/-- PACKING SQUARES IN A RECTILINEAR POLYGON as a decision problem over bitstrings. -/
noncomputable def packingSquaresRectilinearPolygonDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PackingSquaresRectilinearPolygonInstance) x with
  | some i => decide (WellFormed i ∧ PackingSquaresRectilinearPolygonFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PackingSquaresRectilinearPolygon
