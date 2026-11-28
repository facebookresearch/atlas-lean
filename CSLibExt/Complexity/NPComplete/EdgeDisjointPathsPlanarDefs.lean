/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE-DISJOINT PATHS in planar graphs: definitions

Source:
M. Middendorf and F. Pfeiffer, "On the complexity of the disjoint paths problem", Combinatorica
13(1) (1993), 97-107, doi:10.1007/BF01202792 (the edge-disjoint paths problem is NP-complete for
planar graphs, even when the graph together with the demand edges `sᵢtᵢ` is planar);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND40] DISJOINT CONNECTING PATHS (the
vertex-disjoint version).
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeDisjointPathsPlanar

open MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPaths
  (DisjointConnectingPathsInstance Graph)

/-- Well-formedness of an instance: the edge list is simple (endpoints in range, no self-loops,
no repeated or reversed edges), every terminal pair consists of two distinct vertices, and the
graph is planar. -/
def WellFormed (i : DisjointConnectingPathsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ p ∈ i.2.2, p.1 < i.1 ∧ p.2 < i.1 ∧ p.1 ≠ p.2) ∧ (Graph i).IsPlanar

/-- There are paths `pⱼ`, one for each terminal pair `(sⱼ, tⱼ)`, where `pⱼ` is a path in `G` from
`sⱼ` to `tⱼ`, and the paths of different pairs have no edge in common. -/
def EdgeDisjointPathsPlanarFeasible (i : DisjointConnectingPathsInstance) : Prop :=
  ∃ paths : Fin i.2.2.length → (u : Fin i.1) × (v : Fin i.1) × (Graph i).Walk u v,
    (∀ j, ((paths j).1 : ℕ) = (i.2.2.get j).1 ∧ ((paths j).2.1 : ℕ) = (i.2.2.get j).2 ∧
      (paths j).2.2.IsPath) ∧
    ∀ j l, j ≠ l → (paths j).2.2.edges.Disjoint (paths l).2.2.edges

open Classical in
/-- EDGE-DISJOINT PATHS in planar graphs as a decision problem over bitstrings. -/
noncomputable def edgeDisjointPathsPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DisjointConnectingPathsInstance) x with
  | some i => decide (WellFormed i ∧ EdgeDisjointPathsPlanarFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EdgeDisjointPathsPlanar
