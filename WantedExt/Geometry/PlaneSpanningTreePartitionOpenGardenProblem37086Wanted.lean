/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complete geometric graphs not partitionable into plane spanning trees (Open Problem Garden 37086)

Open Problem Garden, Partition of Complete Geometric Graph into Plane Trees (posted by D. R. Wood):
every complete geometric graph with an even number of vertices has a partition of its edge set into
plane (non-crossing) spanning trees.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.Geometry.PlaneSpanningTreePartitionOpenGardenProblem37086Wanted

/-!
Source: Open Problem Garden, Partition of Complete Geometric Graph into Plane Trees (node 37086;
conjecture of Bose, Hurtado, Rivera-Campo and Wood, posted by D. R. Wood),
http://www.openproblemgarden.org/op/partition_of_complete_geometric_graph_into_plane_trees.
UnsolvedMath record UM-00003084 (`OPG-37086`), dataset ulamai/UnsolvedMath v1.8.0.

As on the source page, the vertices are `2n` points in the plane with no three collinear and the
edges are all straight-line segments between them; since a tree on `2n` vertices has `2n - 1` edges,
the conjecture asks for exactly `n` spanning trees. A partition is an edge colouring `c` with `n`
colours whose classes are spanning trees on all `2n` points; plane means that two edges of the same
class with four distinct ends have disjoint segments (edges with a common end meet only there, as no
three points are collinear). Points are in `ℝ × ℝ`; crossing is an affine notion, so the norm does
not matter.
-/

/-- The points `p i` are in general position: pairwise distinct, and no three distinct ones are
collinear. -/
def InGeneralPosition {m : ℕ} (p : Fin m → ℝ × ℝ) : Prop :=
  Function.Injective p ∧
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ¬ Collinear ℝ ({p i, p j, p k} : Set (ℝ × ℝ))

/-- The colouring `c` of the edges `ij` (`i ≠ j`) of the complete geometric graph on the points
`p i` partitions its edge set into `n` plane spanning trees: `c` is symmetric, every colour class
is a spanning tree on all the points, and no two edges of the same colour with four distinct ends
cross (their straight-line segments are disjoint). -/
def IsPlaneSpanningTreePartition {m : ℕ} (p : Fin m → ℝ × ℝ) {n : ℕ}
    (c : Fin m → Fin m → Fin n) : Prop :=
  (∀ i j, c i j = c j i) ∧
    ∀ k : Fin n,
      (SimpleGraph.fromRel fun i j => c i j = k).IsTree ∧
      ∀ i j i' j', i ≠ j → i' ≠ j' → i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
        c i j = k → c i' j' = k → Disjoint (segment ℝ (p i) (p j)) (segment ℝ (p i') (p j'))

/-- The conjecture of Bose, Hurtado, Rivera-Campo and Wood: for every `n ≥ 1`, the edge set of the
complete geometric graph on any `2n` points in general position can be partitioned into `n` plane
spanning trees. -/
def planeSpanningTreePartition : Prop :=
  ∀ n : ℕ, 0 < n → ∀ p : Fin (2 * n) → ℝ × ℝ, InGeneralPosition p →
    ∃ c : Fin (2 * n) → Fin (2 * n) → Fin n, IsPlaneSpanningTreePartition p c

/--
Resolved false: Aichholzer, Obenaus, Orthaber et al. showed that the bumpy wheel sets `BW_{k,ℓ}`
with odd `k ≥ 3` and odd `ℓ ≥ 5` (for example the 16 points of `BW_{3,5}`) are in general position
and their complete geometric graphs cannot be partitioned into `n` plane spanning trees. Source:
Open Problem Garden, Partition of Complete Geometric Graph into Plane Trees (node 37086; conjecture
of Bose, Hurtado, Rivera-Campo and Wood, posted by D. R. Wood),
http://www.openproblemgarden.org/op/partition_of_complete_geometric_graph_into_plane_trees;
resolution: O. Aichholzer, J. Obenaus, J. Orthaber, R. Paul, P. Schnider, R. Steiner, T. Taubner and
B. Vogtenhuber, Edge partitions of complete geometric graphs, 38th Int. Symp. Comput. Geom. (SoCG
2022), LIPIcs 224, paper 6, doi:10.4230/LIPIcs.SoCG.2022.6; J. Obenaus and J. Orthaber,
arXiv:2108.05159, abstract: 'we disprove the long-standing conjecture that any complete geometric
graph on 2n vertices can be partitioned into n plane spanning trees'; arXiv:2108.05159, Theorem 3:
for odd k, l ≥ 3 the bumpy wheel BW_{k,l} (kl + 1 points in general position) cannot be partitioned
into n = (kl + 1)/2 plane spanning trees if and only if l > 3,
https://doi.org/10.4230/LIPIcs.SoCG.2022.6.
-/
public theorem_wanted planeSpanningTreePartition_refuted : ¬ planeSpanningTreePartition

end MathlibExt.Geometry.PlaneSpanningTreePartitionOpenGardenProblem37086Wanted
