/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR INTERCONNECTION ON A GRID with horizontally monotone paths: definitions

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

public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PlanarInterconnectionGridDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonotonePlanarInterconnectionGrid

open PlanarInterconnectionGrid (PlanarInterconnectionGridInstance toSite WellFormed)

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

end MetaMathlibExt.Complexity.NPComplete.MonotonePlanarInterconnectionGrid
