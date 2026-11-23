/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) on unit disk graphs is NP-complete

Source:
J. Díaz, M. D. Penrose, J. Petit and M. Serna, "Linear orderings of random geometric graphs
(extended abstract)", in *Graph-Theoretic Concepts in Computer Science (WG 1999)*, Lecture Notes
in Computer Science 1665, Springer (1999), 291-302, doi:10.1007/3-540-46784-X_28 (Theorem 1:
"Bandwidth, MinCut and VertSep remain NP-complete even when restricted to grid graphs (and
therefore, even when restricted to unit disk graphs)"); journal version: "Approximating layout
problems on random geometric graphs", Journal of Algorithms 39 (2001), 78-116,
doi:10.1006/jagm.2000.1149;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT (the
parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementWanted
public import WantedExt.Complexity.NPComplete.UnitDiskDominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementUnitDiskGraphs

open MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement
  (MinimumCutLinearArrangementInstance MinimumCutLinearArrangementFeasible)
open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode)
open MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet (unitDiskGraph)

/-!
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) on unit disk graphs is NP-complete

INSTANCE: a unit disk graph `G = (V, E)` given with an intersection model, i.e. distinct points
of the plane (the centers of closed disks of diameter one) such that two vertices are adjacent
exactly when their disks intersect, which happens exactly when the centers are at distance at
most `1`; and a positive integer `K`. QUESTION: is there a one-to-one function
`f : V → {1, 2, ..., |V|}` such that for all `i`, `1 ≤ i < |V|`,
`|{{u, v} ∈ E : f(u) ≤ i < f(v)}| ≤ K`, i.e. is the cutwidth of `G` at most `K`?

Díaz, Penrose, Petit and Serna call this problem MinCut. Their Theorem 1 proves it NP-complete
on grid graphs (finite node-induced subgraphs of the infinite grid), which are the unit disk
graphs of their nodes: distinct integer points are at distance at most `1` exactly when they are
grid neighbours. Their reduction draws a planar graph of maximum degree 3 on a grid of
polynomial area, so the resulting points have integer coordinates of polynomial size, and the
problem stays NP-hard with the points in the instance. A layout is a certificate, so the
problem is in NP.

The points have rational coordinates in the encoding of `PlanarKMeansWanted` (`RatCode`), and
the graph of the model is the repository's `UnitDiskDominatingSet.unitDiskGraph` (distinct
points at Euclidean distance at most `1` are adjacent), as in `MaxCutUnitDiskGraphsWanted`. The
instance lists the points, the edges of `G`, and `K`: well-formedness requires positive
denominators, distinct centers, a well-formed MINIMUM CUT LINEAR ARRANGEMENT instance on the
vertices `0, ..., |P| - 1` (a simple edge list and `0 < K`), and that this edge list is exactly
the unit disk graph of the points. The question is that of
`WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementWanted` on `(|P|, E, K)`, reused
unchanged.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the disk centers (pairs of rational coordinates), the edge list of the graph,
and the bound `K`. -/
abbrev MinimumCutLinearArrangementUnitDiskGraphsInstance :=
  List (RatCode × RatCode) × List (ℕ × ℕ) × ℕ

/-- The MINIMUM CUT LINEAR ARRANGEMENT instance `(|P|, E, K)` of the graph. -/
def toMinimumCutLinearArrangement (i : MinimumCutLinearArrangementUnitDiskGraphsInstance) :
    MinimumCutLinearArrangementInstance :=
  (i.1.length, i.2.1, i.2.2)

/-- Well-formedness of an instance: positive denominators; distinct centers; a well-formed
MINIMUM CUT LINEAR ARRANGEMENT instance on the vertices `0, ..., |P| - 1`; and the edge list is
the unit disk graph of the centers. -/
def WellFormed (i : MinimumCutLinearArrangementUnitDiskGraphsInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧ (i.1.map fun p => (p.1.val, p.2.val)).Nodup ∧
    MinimumCutLinearArrangement.WellFormed (toMinimumCutLinearArrangement i) ∧
    Cslib.Complexity.Karp.edgeGraph i.1.length i.2.1 = unitDiskGraph i.1

/-- The cutwidth of the graph is at most `K` (the MINIMUM CUT LINEAR ARRANGEMENT question on
`(|P|, E, K)`). -/
def MinimumCutLinearArrangementUnitDiskGraphsFeasible
    (i : MinimumCutLinearArrangementUnitDiskGraphsInstance) : Prop :=
  MinimumCutLinearArrangementFeasible (toMinimumCutLinearArrangement i)

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT on unit disk graphs as a decision problem over bitstrings. -/
noncomputable def minimumCutLinearArrangementUnitDiskGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementUnitDiskGraphsInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCutLinearArrangementUnitDiskGraphsFeasible i)
  | none => false

/-- **MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) on unit disk graphs is NP-complete.** Source:
Díaz, Penrose, Petit and Serna (1999), Theorem 1. -/
public theorem_wanted minimumCutLinearArrangementUnitDiskGraphs_npComplete :
    minimumCutLinearArrangementUnitDiskGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCutLinearArrangementUnitDiskGraphsDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementUnitDiskGraphs
