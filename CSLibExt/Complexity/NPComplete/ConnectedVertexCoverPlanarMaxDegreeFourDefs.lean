/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED VERTEX COVER on planar graphs of maximum degree 4: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT1] VERTEX COVER, p. 190, comment:
"Variation in which the subgraph induced by V' is required to be connected is also
NP-complete, even for planar graphs with no vertex degree exceeding 4 [Garey and Johnson,
1977a]";
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32(4) (1977), 826-834, doi:10.1137/0132071.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedVertexCoverPlanarMaxDegreeFour

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev ConnectedVertexCoverPlanarMaxDegreeFourInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ConnectedVertexCoverPlanarMaxDegreeFourInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is planar with every vertex degree at most `4`, and `0 < K ≤ |V|`. -/
def WellFormed (i : ConnectedVertexCoverPlanarMaxDegreeFourInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsPlanar ∧ (∀ v, (Graph i).degree v ≤ 4) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at most `K` vertices is a vertex cover of `G` inducing a connected subgraph. -/
def ConnectedVertexCoverPlanarMaxDegreeFourFeasible
    (i : ConnectedVertexCoverPlanarMaxDegreeFourInstance) : Prop :=
  ∃ s : Finset (Fin i.1), s.card ≤ i.2.2 ∧ (Graph i).IsVertexCover (s : Set (Fin i.1)) ∧
    ((Graph i).induce (s : Set (Fin i.1))).Connected

open Classical in
/-- CONNECTED VERTEX COVER on planar graphs of maximum degree 4 as a decision problem over
bitstrings. -/
noncomputable def connectedVertexCoverPlanarMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConnectedVertexCoverPlanarMaxDegreeFourInstance) x with
  | some i => decide (WellFormed i ∧ ConnectedVertexCoverPlanarMaxDegreeFourFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConnectedVertexCoverPlanarMaxDegreeFour
