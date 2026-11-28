/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on 2-connected cubic planar graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, the problem
restricted here;
B. Mohar, "Face covers and the genus problem for apex graphs", Journal of Combinatorial Theory,
Series B 82(1) (2001), 102-117, doi:10.1006/jctb.2000.2026, Theorem 4.1(a).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoConnectedCubicPlanar

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev IndependentSetTwoConnectedCubicPlanarInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentSetTwoConnectedCubicPlanarInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is 2-connected, cubic and planar, and `0 < K ≤ |V|`. -/
def WellFormed (i : IndependentSetTwoConnectedCubicPlanarInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsVertexConnected 2 ∧ (Graph i).IsRegularOfDegree 3 ∧ (Graph i).IsPlanar ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices contains no two adjacent vertices. -/
def IndependentSetTwoConnectedCubicPlanarFeasible
    (i : IndependentSetTwoConnectedCubicPlanarInstance) : Prop :=
  ∃ s : Finset (Fin i.1), i.2.2 ≤ s.card ∧ (Graph i).IsIndepSet (s : Set (Fin i.1))

open Classical in
/-- INDEPENDENT SET on 2-connected cubic planar graphs as a decision problem over bitstrings. -/
noncomputable def independentSetTwoConnectedCubicPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentSetTwoConnectedCubicPlanarInstance) x with
  | some i => decide (WellFormed i ∧ IndependentSetTwoConnectedCubicPlanarFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoConnectedCubicPlanar
