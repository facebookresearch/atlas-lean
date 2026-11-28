/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for line graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET (comment: the related EDGE
DOMINATING SET problem "is NP-complete, even for planar or bipartite graphs of maximum degree 3"
[Yannakakis and Gavril]); D. S. Johnson, "The NP-completeness column: an ongoing guide" (sixteenth
edition), Journal of Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row
"Edge (or Line)", column "DomSet": "N [GJ]"); M. Yannakakis and F. Gavril, "Edge dominating sets
in graphs", SIAM Journal on Applied Mathematics 38 (1980), 364-372, doi:10.1137/0138030.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetLineGraphs

open MetaMathlibExt.Complexity.NPComplete.DominatingSet
  (DominatingSetInstance Graph DominatingSetFeasible)

/-- Well-formedness of an instance: the parent's simple edge list, `0 < K ≤ |V|`, and the graph
is a line graph. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧
    MetaMathlibExt.SimpleGraph.IsLineGraph (Graph i)

open Classical in
/-- DOMINATING SET for line graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetLineGraphs
