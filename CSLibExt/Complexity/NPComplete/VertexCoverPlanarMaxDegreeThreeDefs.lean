/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX COVER on planar graphs of maximum degree 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT1] VERTEX COVER, p. 190, comment
("Equivalent complexity to INDEPENDENT SET with respect to restrictions on G"), and problem
[GT20] INDEPENDENT SET, p. 195, comment ("Remains NP-complete for cubic planar graphs [Garey,
Johnson, and Stockmeyer, 1976], [Garey and Johnson, 1977a], [Maier and Storer, 1977]");
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1;
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32(4) (1977), 826-834, doi:10.1137/0132071;
B. Mohar, "Face covers and the genus problem for apex graphs", Journal of Combinatorial Theory,
Series B 82(1) (2001), 102-117, doi:10.1006/jctb.2000.2026, Theorem 4.1(a).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexCoverPlanarMaxDegreeThree

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev VertexCoverPlanarMaxDegreeThreeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : VertexCoverPlanarMaxDegreeThreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is planar with every vertex degree at most `3`, and `0 < K ≤ |V|`. -/
def WellFormed (i : VertexCoverPlanarMaxDegreeThreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsPlanar ∧ (∀ v, (Graph i).degree v ≤ 3) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at most `K` vertices is a vertex cover of `G`. -/
def VertexCoverPlanarMaxDegreeThreeFeasible (i : VertexCoverPlanarMaxDegreeThreeInstance) :
    Prop :=
  ∃ s : Finset (Fin i.1), s.card ≤ i.2.2 ∧ (Graph i).IsVertexCover (s : Set (Fin i.1))

open Classical in
/-- VERTEX COVER on planar graphs of maximum degree 3 as a decision problem over bitstrings. -/
noncomputable def vertexCoverPlanarMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := VertexCoverPlanarMaxDegreeThreeInstance) x with
  | some i => decide (WellFormed i ∧ VertexCoverPlanarMaxDegreeThreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.VertexCoverPlanarMaxDegreeThree
