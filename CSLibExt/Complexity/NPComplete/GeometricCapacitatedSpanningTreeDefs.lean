/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC CAPACITATED SPANNING TREE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND6] GEOMETRIC CAPACITATED SPANNING
TREE (reference [Papadimitriou, 1976c], transformation from X3C);
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTree

/-- An instance `(P, p₀, r, c, B)`: the points (encoded as in GEOMETRIC TRAVELING SALESMAN),
the index of `p₀`, the requirements `r(p)` of the points in order, the capacity `c`, and the
bound `B`. -/
abbrev GeometricCapacitatedSpanningTreeInstance :=
  List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ × List ℕ × ℕ × ℕ

/-- The points of the instance in `Z × Z`. -/
def points (i : GeometricCapacitatedSpanningTreeInstance) : List (ℤ × ℤ) :=
  i.1.map GeometricTravelingSalesman.point

/-- The discretized Euclidean distance between the points with indices `a` and `b`. -/
noncomputable def pointDist (i : GeometricCapacitatedSpanningTreeInstance) (a b : Fin i.1.length) :
    ℕ :=
  GeometricTravelingSalesman.discreteDist ((points i).getD a (0, 0)) ((points i).getD b (0, 0))

/-- Well-formedness of an instance: the points are nonempty and distinct, `p₀` is one of them,
there is one requirement per point, and `c` and `B` are positive. -/
def WellFormed (i : GeometricCapacitatedSpanningTreeInstance) : Prop :=
  0 < i.1.length ∧ (points i).Nodup ∧ i.2.1 < i.1.length ∧ i.2.2.1.length = i.1.length ∧
    0 < i.2.2.2.1 ∧ 0 < i.2.2.2.2

open Classical in
/-- Some spanning tree `T` of the complete graph on the points has total discretized Euclidean
length at most `B`, and for each edge `e` of `T` the requirements of the points whose path to
`p₀` in `T` contains `e` sum to at most `c`. -/
def GeometricCapacitatedSpanningTreeFeasible (i : GeometricCapacitatedSpanningTreeInstance) :
    Prop :=
  ∃ hp : i.2.1 < i.1.length, ∃ T : SimpleGraph (Fin i.1.length), T.IsTree ∧
    (∑ a, ∑ b, if T.Adj a b ∧ a < b then pointDist i a b else 0) ≤ i.2.2.2.2 ∧
    ∀ e ∈ T.edgeSet,
      ∑ u ∈ Finset.univ.filter (fun u => ∃ p : T.Walk u ⟨i.2.1, hp⟩, p.IsPath ∧ e ∈ p.edges),
        i.2.2.1.getD u 0 ≤ i.2.2.2.1

open Classical in
/-- GEOMETRIC CAPACITATED SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def geometricCapacitatedSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeometricCapacitatedSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ GeometricCapacitatedSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTree
