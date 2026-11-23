/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE-DISJOINT PATHS in planar graphs is NP-complete

Source:
M. Middendorf and F. Pfeiffer, "On the complexity of the disjoint paths problem", Combinatorica
13(1) (1993), 97-107, doi:10.1007/BF01202792 (the edge-disjoint paths problem is NP-complete for
planar graphs, even when the graph together with the demand edges `sᵢtᵢ` is planar);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND40] DISJOINT CONNECTING PATHS (the
vertex-disjoint version).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DisjointConnectingPathsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeDisjointPathsPlanar

open MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPaths
  (DisjointConnectingPathsInstance Graph)

/-!
# EDGE-DISJOINT PATHS in planar graphs is NP-complete

INSTANCE: a planar graph `G = (V, E)` and terminal pairs `(s₁, t₁), ..., (sₖ, tₖ)` of vertices,
`sᵢ ≠ tᵢ`.
QUESTION: does `G` contain `k` pairwise edge-disjoint paths, the `i`-th connecting `sᵢ` and `tᵢ`?

This is the edge-disjoint variant of DISJOINT CONNECTING PATHS ([ND40],
`DisjointConnectingPathsWanted`), restricted to planar graphs. The instance type and the graph
are those of `DisjointConnectingPathsWanted`
(`DisjointConnectingPaths.DisjointConnectingPathsInstance`: vertex count `n`, edge list, list of
pairs; `DisjointConnectingPaths.Graph`: the simple graph `Cslib.Complexity.Karp.edgeGraph` on
`Fin n`). Unlike [ND40], whose pairs are disjoint, terminal
pairs may share vertices and may repeat, as demands of the edge-disjoint problem may; each pair
has two distinct vertices. A path is a Mathlib `SimpleGraph.Walk` with `IsPath`, and two paths are
edge-disjoint when their edge lists (`SimpleGraph.Walk.edges`) are disjoint. Planarity is
MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's
theorem exists exactly for planar graphs).

Membership in NP: the paths are a polynomial certificate and planarity is decidable in linear
time (Hopcroft and Tarjan, J. ACM 21 (1974), 549-568).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **EDGE-DISJOINT PATHS in planar graphs is NP-complete.** Source: Middendorf and Pfeiffer
(1993); Garey and Johnson (1979), [ND40] (vertex-disjoint version). -/
public theorem_wanted edgeDisjointPathsPlanar_npComplete :
    edgeDisjointPathsPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeDisjointPathsPlanarDec

end MetaMathlibExt.Complexity.NPComplete.EdgeDisjointPathsPlanar
