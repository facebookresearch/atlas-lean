/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC CONNECTED DOMINATING SET: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND48] GEOMETRIC CONNECTED
DOMINATING SET;
D. Lichtenstein, "Planar formulae and their uses", SIAM Journal on Computing 11 (1982),
329-343, doi:10.1137/0211025.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSet

open GeometricTravelingSalesman (point)

/-- An instance: the points of `P` as `((x⁺, x⁻), (y⁺, y⁻))`, standing for
`(x⁺ - x⁻, y⁺ - y⁻)`, the distance bound `B`, and the size bound `K`. -/
abbrev GeometricConnectedDominatingSetInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ × ℕ

/-- The squared Euclidean distance `(x₁ - x₂)² + (y₁ - y₂)²` of two integer points. -/
def sqDist (p q : ℤ × ℤ) : ℤ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The distance-`B` graph on the points of `P`: two distinct points are adjacent when their
Euclidean distance is at most `B`, that is, when their squared distance is at most `B²`. -/
def Graph (i : GeometricConnectedDominatingSetInstance) : SimpleGraph (Fin i.1.length) :=
  SimpleGraph.fromRel fun a b => sqDist (point i.1[a]) (point i.1[b]) ≤ (i.2.1 : ℤ) ^ 2

/-- Well-formedness of an instance: the points of `P` are distinct, and `B` and `K` are
positive. -/
def WellFormed (i : GeometricConnectedDominatingSetInstance) : Prop :=
  (i.1.map point).Nodup ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Some subset `P' ⊆ P` of at most `K` points dominates the distance-`B` graph, and the
subgraph it induces is connected. -/
def GeometricConnectedDominatingSetFeasible (i : GeometricConnectedDominatingSetInstance) :
    Prop :=
  ∃ P' : Finset (Fin i.1.length), P'.card ≤ i.2.2 ∧ (Graph i).IsDominating ↑P' ∧
    ((Graph i).induce (↑P' : Set (Fin i.1.length))).Connected

open Classical in
/-- GEOMETRIC CONNECTED DOMINATING SET as a decision problem over bitstrings. -/
noncomputable def geometricConnectedDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeometricConnectedDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ GeometricConnectedDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSet
