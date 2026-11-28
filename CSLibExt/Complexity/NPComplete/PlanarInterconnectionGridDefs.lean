/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR INTERCONNECTION ON A GRID: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND40] DISJOINT CONNECTING PATHS
(the parent graph problem);
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fifth edition), Journal of
Algorithms 3 (1982), 381-395, doi:10.1016/0196-6774(82)90032-3, problem [6] PLANAR
INTERCONNECTION ON A GRID (reference: Richards, and Kramer and van Leeuwen; transformation
from PLANAR 3SAT);
D. Richards, "Complexity of single-layer routing", IEEE Transactions on Computers C-33 (1984),
286-288, doi:10.1109/TC.1984.1676428;
M. R. Kramer and J. van Leeuwen, "Wire-routing is NP-complete", Report RUU-CS-82-4,
Department of Computer Science, University of Utrecht (1982).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarInterconnectionGrid

/-- An encoded grid point: its x- and y-coordinates, each as (positive part, negative part). -/
abbrev EncodedPoint := (ℕ × ℕ) × (ℕ × ℕ)

/-- An instance: the list of pairs `(pᵢ, qᵢ)` of grid points to connect. -/
abbrev PlanarInterconnectionGridInstance := List (EncodedPoint × EncodedPoint)

/-- The grid point `(x, y) ∈ ℤ²` an encoded point stands for. -/
def toSite (p : EncodedPoint) : StatMech.Lattice.Site 2 :=
  ![(p.1.1 : ℤ) - p.1.2, (p.2.1 : ℤ) - p.2.2]

/-- Well-formedness of an instance: the pairs are disjoint, i.e. the `2n` grid points
`p₁, q₁, ..., pₙ, qₙ` are pairwise distinct. -/
def WellFormed (i : PlanarInterconnectionGridInstance) : Prop :=
  (i.flatMap fun pq => [toSite pq.1, toSite pq.2]).Nodup

/-- Every pair `(pⱼ, qⱼ)` is joined by a grid path, and the paths of different pairs share no
grid point. -/
def PlanarInterconnectionGridFeasible (i : PlanarInterconnectionGridInstance) : Prop :=
  ∃ paths : ∀ j : Fin i.length,
      (StatMech.Lattice.hypercubicLattice 2).Walk (toSite (i.get j).1) (toSite (i.get j).2),
    (∀ j, (paths j).IsPath) ∧ ∀ j l, j ≠ l → (paths j).support.Disjoint (paths l).support

open Classical in
/-- PLANAR INTERCONNECTION ON A GRID as a decision problem over bitstrings. -/
noncomputable def planarInterconnectionGridDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarInterconnectionGridInstance) x with
  | some i => decide (WellFormed i ∧ PlanarInterconnectionGridFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarInterconnectionGrid
