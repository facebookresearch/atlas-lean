/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR INTERCONNECTION ON A GRID with horizontally monotone paths is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (tenth edition), Journal of
Algorithms 5 (1984), 147-160, doi:10.1016/0196-6774(84)90045-2, update to PLANAR
INTERCONNECTION ON A GRID [Dec. 1982] (attribution: K. Karplus, "CHISEL: An extension to the
programming language C for VLSI layout", Report No. STAN-CS-82-959, Department of Computer
Science, Stanford University (1982); that report was not available to us);
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fifth edition), Journal of
Algorithms 3 (1982), 381-395, doi:10.1016/0196-6774(82)90032-3, problem [6] PLANAR
INTERCONNECTION ON A GRID (the parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PlanarInterconnectionGridWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonotonePlanarInterconnectionGrid

open PlanarInterconnectionGrid (PlanarInterconnectionGridInstance toSite WellFormed)

/-!
# PLANAR INTERCONNECTION ON A GRID with horizontally monotone paths is NP-complete

INSTANCE: a set `P = {(p₁, q₁), ..., (pₙ, qₙ)}` of disjoint pairs of integer-coordinate grid
points. QUESTION: is there a way of connecting each pair of grid points in `P` by a path made
up of grid segments, so that no two of the paths intersect, where each path is "monotone" in
the horizontal direction?

Johnson's tenth column reports that PLANAR INTERCONNECTION ON A GRID is "also NP-complete even
if each interconnecting path must be 'monotone' in the horizontal direction (must proceed from
left to right without turning back)", crediting Karplus (1982).

This is PLANAR INTERCONNECTION ON A GRID (`PlanarInterconnectionGridWanted`) with the extra
requirement on the paths. The instance, the grid point of an encoded point
(`PlanarInterconnectionGrid.toSite`) and the well-formedness condition
(`PlanarInterconnectionGrid.WellFormed`: the `2n` points `p₁, q₁, ..., pₙ, qₙ` are pairwise
distinct) are the parent's, unchanged. The question is the parent's (each pair joined by a path
of the square grid `StatMech.Lattice.hypercubicLattice 2`, paths of different pairs sharing no
grid point) with one more conjunct per path: the path is horizontally monotone. A pair is
unordered, so "proceeds from left to right without turning back" says that, read from its left
end to its right end, the path never decreases its x-coordinate; for the path from `pᵢ` to
`qᵢ` this means that its x-coordinate is monotone (never decreasing) or antitone (never
increasing) along the path (`IsHorizontallyMonotone`). Vertical grid segments are allowed in
either direction; a pair whose two points have the same x-coordinate must be joined by the
vertical segment between them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A walk in the square grid is horizontally monotone when the x-coordinate of its `k`-th
vertex never decreases in `k`, or never increases in `k`: read from its left end to its right
end, it never turns back. (`SimpleGraph.Walk.getVert k` is the end vertex for every `k` past
the length, so only the walk's own vertices matter.) -/
def IsHorizontallyMonotone {p q : StatMech.Lattice.Site 2}
    (w : (StatMech.Lattice.hypercubicLattice 2).Walk p q) : Prop :=
  Monotone (fun k => w.getVert k 0) ∨ Antitone (fun k => w.getVert k 0)

/-- Every pair `(pⱼ, qⱼ)` is joined by a horizontally monotone grid path, and the paths of
different pairs share no grid point. -/
def MonotonePlanarInterconnectionGridFeasible (i : PlanarInterconnectionGridInstance) :
    Prop :=
  ∃ paths : ∀ j : Fin i.length,
      (StatMech.Lattice.hypercubicLattice 2).Walk (toSite (i.get j).1) (toSite (i.get j).2),
    (∀ j, (paths j).IsPath ∧ IsHorizontallyMonotone (paths j)) ∧
      ∀ j l, j ≠ l → (paths j).support.Disjoint (paths l).support

open Classical in
/-- PLANAR INTERCONNECTION ON A GRID with horizontally monotone paths as a decision problem over
bitstrings. -/
noncomputable def monotonePlanarInterconnectionGridDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarInterconnectionGridInstance) x with
  | some i => decide (WellFormed i ∧ MonotonePlanarInterconnectionGridFeasible i)
  | none => false

/-- **PLANAR INTERCONNECTION ON A GRID with horizontally monotone paths is NP-complete.**
Source: Johnson, NP-completeness column (tenth edition, 1984), update to PLANAR INTERCONNECTION
ON A GRID, crediting Karplus (1982). -/
public theorem_wanted monotonePlanarInterconnectionGrid_npComplete :
    monotonePlanarInterconnectionGridDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L monotonePlanarInterconnectionGridDec

end MetaMathlibExt.Complexity.NPComplete.MonotonePlanarInterconnectionGrid
