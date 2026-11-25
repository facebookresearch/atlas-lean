/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PACKING SQUARES IN A RECTILINEAR POLYGON is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Set.Prod
public import WantedExt.Complexity.NPComplete.PolyominoPackingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PackingSquaresRectilinearPolygon

/-!
# PACKING SQUARES IN A RECTILINEAR POLYGON is NP-complete

INSTANCE: a rectilinear polygon `P` made of unit cells of the integer grid, i.e. a polyomino
(holes allowed), and positive integers `d` and `K`. QUESTION: can `K` pairwise disjoint
(non-overlapping) axis-parallel `d × d` squares be placed inside `P`?

Fowler, Paterson and Tanimoto proved this NP-complete by a transformation from PLANAR 3SAT; as
Berman et al. record (Section 1), they "proved that finding the maximum number of `3 × 3` squares
of functioning cells is NP-complete", and Berman et al. extend the result to every fixed
rectangle other than `1 × 1` and `1 × 2`, in particular to `d × d` squares for every fixed
`d ≥ 2` (Section 4, the optimal tile salvage problem: "Consider a `√N × √N` region of the plane
tiled with unit squares, some of which have been removed ... find the maximum number of
functional, non-overlapping `x × y` tiled rectangles"). With `d` part of the input, the problem
is NP-hard by fixing `d = 2` (or `3`), and a placement of the `K` squares is a certificate.

Aamand, Abrahamsen, Ahle and Rasmussen (Section 1) record both results as packing squares into
"a polyomino (with holes)", where (abstract) "A polyomino is a polygonal region with axis parallel
edges and corners of integral coordinates, which may have holes", and note that these results
assume "the container `P` is represented ... as a list of the
individual cells forming the interior of `P`". The polygon is accordingly the list of its cells
`(a, b) ∈ ℕ × ℕ`, the cell `[a, a + 1] × [b, b + 1]`, and it must be a polyomino: a nonempty set
of cells connected through shared edges, the repository's `isPolycubeCells 2` applied to the
cells as lattice points (`PolyominoPacking.pieceCells`, as for the pieces of
`PolyominoPackingWanted`); holes are allowed. The input size bounds the area, which the
reductions keep polynomial (the problem is NP-complete in the strong sense). A square is placed
with its lower-left cell at `c` and covers the cells
`Set.Ico c.1 (c.1 + d) ×ˢ Set.Ico c.2 (c.2 + d)`; squares must lie in the polygon and may not
share a cell, i.e. their interiors are disjoint. Grid placements lose nothing: rounding the
lower-left corner of a square placed anywhere in the plane down to the grid keeps it inside a
polygon made of unit cells (each cell it then covers met the original square in an interior
point) and keeps disjoint squares disjoint (since `d` is an integer).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PACKING SQUARES IN A RECTILINEAR POLYGON is NP-complete.** Source: Fowler, Paterson and
Tanimoto (1981); Berman, Johnson, Leighton, Shor and Snyder (1990), Sections 1 and 4; Aamand,
Abrahamsen, Ahle and Rasmussen (2023), Section 1. -/
public theorem_wanted packingSquaresRectilinearPolygon_npComplete :
    packingSquaresRectilinearPolygonDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L packingSquaresRectilinearPolygonDec

end MetaMathlibExt.Complexity.NPComplete.PackingSquaresRectilinearPolygon
