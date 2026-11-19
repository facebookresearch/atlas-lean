/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR INTERCONNECTION ON A GRID is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarInterconnectionGrid

/-!
# PLANAR INTERCONNECTION ON A GRID is NP-complete

INSTANCE: a set `P = {(p₁, q₁), ..., (pₙ, qₙ)}` of disjoint pairs of integer-coordinate grid
points. QUESTION: is there a way of connecting each pair of grid points in `P` by a path made
up of grid segments, so that no two of the paths intersect?

The grid is the column's "standard rectilinear grid, where each integer-coordinate point is a
grid point, connected by length-1 grid segments to its four immediate neighbors": the
hypercubic lattice `StatMech.Lattice.hypercubicLattice 2` on `ℤ²` from `MathlibExt` (as in
`UnitLengthTreeGridEmbeddingWanted`), whose edges join points at `ℓ¹` distance 1. A path made
up of grid segments from `pᵢ` to `qᵢ` is a path (`SimpleGraph.Walk.IsPath`) in that graph.
Two length-1 grid segments meet, if at all, in a grid point or in a whole common segment
(whose ends are grid points), so two such paths intersect exactly when they share a grid
point: "no two of the paths intersect" is disjointness of the vertex lists
(`SimpleGraph.Walk.support`), as in `DisjointConnectingPathsWanted` ([ND40], of which this is
the restriction to the grid). "Disjoint pairs" means the `2n` points `p₁, q₁, ..., pₙ, qₙ` are
pairwise distinct.

Each integer coordinate is encoded as a pair of naturals `(positive part, negative part)`
representing their difference, as in `ZeroOneILPWanted`; a point is a pair of such
coordinates, and `P` is a list of pairs of points.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PLANAR INTERCONNECTION ON A GRID is NP-complete.** Source: Johnson, NP-completeness column
(1982), problem [6]; Richards (1984); Kramer and van Leeuwen (1982). -/
public theorem_wanted planarInterconnectionGrid_npComplete :
    planarInterconnectionGridDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarInterconnectionGridDec

end MetaMathlibExt.Complexity.NPComplete.PlanarInterconnectionGrid
