/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC CONNECTED DOMINATING SET under the L₁ and L∞ metrics: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND48] GEOMETRIC CONNECTED
DOMINATING SET, comment (p. 219): "Remains NP-complete if the Euclidean metric is replaced by
the `L₁` rectilinear metric or the `L∞` metric [Garey and Johnson, ——]" (unpublished).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricConnectedDominatingSetDefs
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinityDefs
public import CSLibExt.Complexity.NPComplete.RectilinearTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSetL1LInfinity

open GeometricTravelingSalesman (point)
open GeometricConnectedDominatingSet (GeometricConnectedDominatingSetInstance WellFormed)
open GeometricTravelingSalesmanLInfinity (chebyshevDist)
open RectilinearTravelingSalesman (rectilinearDist)

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

end MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSetL1LInfinity
