/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for line graphs is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import WantedExt.Complexity.NPComplete.DominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetLineGraphs

open MetaMathlibExt.Complexity.NPComplete.DominatingSet
  (DominatingSetInstance Graph DominatingSetFeasible)

/-!
# DOMINATING SET for line graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is an edge (line) graph, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that for all `u ∈ V - V'` there is a `v ∈ V'` with `{u, v} ∈ E`?

This is DOMINATING SET ([GT2], `DominatingSetWanted`) restricted to line graphs: a dominating set
of the line graph `L(H)` is exactly an edge dominating set of `H`, so the entry's EDGE DOMINATING
SET result is the hint Johnson's table cites. The instance type, `DominatingSet.Graph`,
`DominatingSet.WellFormed` (simple edge list) and `DominatingSet.DominatingSetFeasible` are the
parent's, unchanged; `WellFormed` adds Garey and Johnson's bounds `0 < K ≤ |V|` (as in
`DominatingSetGridGraphsWanted`) and `MetaMathlibExt.SimpleGraph.IsLineGraph` (from
`MathlibExt.Combinatorics.SimpleGraph.LineGraph`: isomorphic to Mathlib's `SimpleGraph.lineGraph`
of a graph on some `Fin k`), as in `LineGraphHamiltonianCircuitWanted`. The instance is the line
graph itself.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **DOMINATING SET is NP-complete for line graphs.** Source: Garey and Johnson (1979), [GT2],
comment; Johnson, NP-completeness column (1985), Table 1; Yannakakis and Gavril (1980). -/
public theorem_wanted dominatingSetLineGraphs_npComplete :
    dominatingSetLineGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetLineGraphsDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetLineGraphs
