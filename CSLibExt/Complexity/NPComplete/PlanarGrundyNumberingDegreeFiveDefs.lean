/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH GRUNDY NUMBERING for planar digraphs with in- and out-degrees at most 5: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT56] GRAPH GRUNDY NUMBERING,
comment: "Remains NP-complete when restricted to planar graphs in which no vertex has in- or
out-degree exceeding 5 [Fraenkel and Yesha, 1977]";
A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, dout ≤ 2, din ≤ 2 are NP-complete",
Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2 (a subclass).
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeBoundedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeFive

open GraphGrundyNumbering (GraphGrundyNumberingInstance GraphGrundyNumberingFeasible)
open PlanarGrundyNumberingDegreeBounded (inDegree outDegree)

/-- Well-formedness of an instance: a well-formed GRAPH GRUNDY NUMBERING instance whose
underlying graph is planar and in which every vertex has in-degree and out-degree at most `5`. -/
def WellFormed (i : GraphGrundyNumberingInstance) : Prop :=
  GraphGrundyNumbering.WellFormed i ∧
    (SimpleGraph.fromRel (GraphGrundyNumbering.Graph i).Adj).IsPlanar ∧
    ∀ v, inDegree i v ≤ 5 ∧ outDegree i v ≤ 5

open Classical in
/-- GRAPH GRUNDY NUMBERING for planar digraphs with in- and out-degrees at most `5` as a
decision problem over bitstrings. -/
noncomputable def planarGrundyNumberingDegreeFiveDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphGrundyNumberingInstance) x with
  | some i => decide (WellFormed i ∧ GraphGrundyNumberingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarGrundyNumberingDegreeFive
