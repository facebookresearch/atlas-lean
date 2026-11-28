/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH GRUNDY NUMBERING for planar digraphs with degree bounds: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT56];
A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, dout ≤ 2, din ≤ 2 are NP-complete",
Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.GraphGrundyNumberingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeBounded

/-- The out-degree of `v`: the number of arcs leaving `v`. -/
def outDegree (i : GraphGrundyNumbering.GraphGrundyNumberingInstance) (v : Fin i.1) : ℕ :=
  (Finset.univ.filter fun u : Fin i.1 => ((v : ℕ), (u : ℕ)) ∈ i.2).card

/-- The in-degree of `v`: the number of arcs entering `v`. -/
def inDegree (i : GraphGrundyNumbering.GraphGrundyNumberingInstance) (v : Fin i.1) : ℕ :=
  (Finset.univ.filter fun u : Fin i.1 => ((u : ℕ), (v : ℕ)) ∈ i.2).card

/-- Well-formedness of an instance: the parent's (no repeated arcs, endpoints are vertices, no
loops); the underlying undirected graph is planar; every vertex has total degree at most `3`,
in-degree at most `2` and out-degree at most `2`. -/
def WellFormed (i : GraphGrundyNumbering.GraphGrundyNumberingInstance) : Prop :=
  GraphGrundyNumbering.WellFormed i ∧
    (SimpleGraph.fromRel (GraphGrundyNumbering.Graph i).Adj).IsPlanar ∧
    ∀ v, inDegree i v + outDegree i v ≤ 3 ∧ inDegree i v ≤ 2 ∧ outDegree i v ≤ 2

open Classical in
/-- GRAPH GRUNDY NUMBERING for planar digraphs with degree bounds as a decision problem over
bitstrings. -/
noncomputable def planarGrundyNumberingDegreeBoundedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphGrundyNumbering.GraphGrundyNumberingInstance) x with
  | some i => decide (WellFormed i ∧ GraphGrundyNumbering.GraphGrundyNumberingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeBounded
