/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC CONNECTED DOMINATING SET under the L₁ and L∞ metrics is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND48] GEOMETRIC CONNECTED
DOMINATING SET, comment (p. 219): "Remains NP-complete if the Euclidean metric is replaced by
the `L₁` rectilinear metric or the `L∞` metric [Garey and Johnson, ——]" (unpublished).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GeometricConnectedDominatingSetWanted
public import WantedExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinityWanted
public import WantedExt.Complexity.NPComplete.RectilinearTravelingSalesmanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSetL1LInfinity

open GeometricTravelingSalesman (point)
open GeometricConnectedDominatingSet (GeometricConnectedDominatingSetInstance WellFormed)
open GeometricTravelingSalesmanLInfinity (chebyshevDist)
open RectilinearTravelingSalesman (rectilinearDist)

/-!
# GEOMETRIC CONNECTED DOMINATING SET under the L₁ and L∞ metrics is NP-complete

INSTANCE: a set `P ⊆ Z × Z` of points in the plane, and positive integers `B` and `K`.
QUESTION: is there a subset `P' ⊆ P` with `|P'| ≤ K` such that all points in `P - P'` are within
distance `B` of some point in `P'`, and such that the graph `G = (P', E)`, with an edge between
two points in `P'` if and only if they are within distance `B` of each other, is connected? Here
the distance is the `L₁` (rectilinear) metric `|x₁ - x₂| + |y₁ - y₂|` in the first problem and the
`L∞` metric `max (|x₁ - x₂|, |y₁ - y₂|)` in the second.

These are the two variants of GEOMETRIC CONNECTED DOMINATING SET
(`WantedExt.Complexity.NPComplete.GeometricConnectedDominatingSetWanted`, GJ [ND48]) recorded in
the comment of [ND48], stated in one module with one `theorem_wanted` each. The instance type and
`WellFormed` (distinct points, `0 < B`, `0 < K`) are reused unchanged from the Euclidean problem,
and the question has the same shape: `P'` dominates the distance-`B` graph of `P`
(`SimpleGraph.IsDominating`), and the subgraph induced on `P'` is `SimpleGraph.Connected`; only
the distance changes. The two distances are those of the [ND23] comment variants on the same
point encoding: `rectilinearDist` of `RectilinearTravelingSalesmanWanted` and `chebyshevDist` of
`GeometricTravelingSalesmanLInfinityWanted`. As in the Euclidean problem, the empty point set is
a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The `L₁` distance-`B` graph on the points of `P`: two distinct points are adjacent when
`|x₁ - x₂| + |y₁ - y₂| ≤ B`. -/
def l1Graph (i : GeometricConnectedDominatingSetInstance) : SimpleGraph (Fin i.1.length) :=
  SimpleGraph.fromRel fun a b => rectilinearDist (point i.1[a]) (point i.1[b]) ≤ i.2.1

/-- The `L∞` distance-`B` graph on the points of `P`: two distinct points are adjacent when
`max (|x₁ - x₂|, |y₁ - y₂|) ≤ B`. -/
def lInfinityGraph (i : GeometricConnectedDominatingSetInstance) : SimpleGraph (Fin i.1.length) :=
  SimpleGraph.fromRel fun a b => chebyshevDist (point i.1[a]) (point i.1[b]) ≤ i.2.1

/-- Under the `L₁` metric, some subset `P' ⊆ P` of at most `K` points dominates the
distance-`B` graph, and the subgraph it induces is connected. -/
def L1Feasible (i : GeometricConnectedDominatingSetInstance) : Prop :=
  ∃ P' : Finset (Fin i.1.length), P'.card ≤ i.2.2 ∧ (l1Graph i).IsDominating ↑P' ∧
    ((l1Graph i).induce (↑P' : Set (Fin i.1.length))).Connected

/-- Under the `L∞` metric, some subset `P' ⊆ P` of at most `K` points dominates the
distance-`B` graph, and the subgraph it induces is connected. -/
def LInfinityFeasible (i : GeometricConnectedDominatingSetInstance) : Prop :=
  ∃ P' : Finset (Fin i.1.length), P'.card ≤ i.2.2 ∧ (lInfinityGraph i).IsDominating ↑P' ∧
    ((lInfinityGraph i).induce (↑P' : Set (Fin i.1.length))).Connected

open Classical in
/-- GEOMETRIC CONNECTED DOMINATING SET under the `L₁` metric as a decision problem over
bitstrings. -/
noncomputable def l1Dec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeometricConnectedDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ L1Feasible i)
  | none => false

open Classical in
/-- GEOMETRIC CONNECTED DOMINATING SET under the `L∞` metric as a decision problem over
bitstrings. -/
noncomputable def lInfinityDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeometricConnectedDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ LInfinityFeasible i)
  | none => false

/-- **GEOMETRIC CONNECTED DOMINATING SET under the `L₁` metric is NP-complete.** Source: Garey
and Johnson (1979), [ND48], comment. -/
public theorem_wanted l1_npComplete :
    l1Dec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L l1Dec

/-- **GEOMETRIC CONNECTED DOMINATING SET under the `L∞` metric is NP-complete.** Source: Garey
and Johnson (1979), [ND48], comment. -/
public theorem_wanted lInfinity_npComplete :
    lInfinityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lInfinityDec

end MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSetL1LInfinity
