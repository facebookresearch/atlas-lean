/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL DOMINATING SET on bipartite graphs is NP-complete

Source:
J. Pfaff, R. C. Laskar and S. T. Hedetniemi, "NP-completeness of total and connected domination
and irredundance for bipartite graphs", Technical Report 428, Department of Mathematical
Sciences, Clemson University (1983) (the original proof; not available online);
M. A. Shalu and V. K. Kirubakaran, "Total domination and open packing in some subclasses of
bipartite graphs", Journal of Combinatorial Optimization 50(5) (2025), article 44,
doi:10.1007/s10878-025-01360-w (NP-completeness on a subclass of bipartite graphs; cites the
technical report).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import WantedExt.Complexity.NPComplete.TotalDominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalDominatingSetBipartite

open MetaMathlibExt.Complexity.NPComplete.TotalDominatingSet

/-!
# TOTAL DOMINATING SET on bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` with no isolated vertices, and a positive integer
`K ≤ |V|`. QUESTION: does `G` have a total dominating set of size at most `K`, i.e. a set
`D ⊆ V` with `|D| ≤ K` such that every vertex of `V` (including those in `D`) is adjacent to a
vertex of `D`?

Pfaff, Laskar and Hedetniemi proved this problem NP-complete in a 1983 Clemson technical report,
which is not available online. Shalu and Kirubakaran (abstract): "Given a graph `G` and a
positive integer `k ≤ |V(G)|`, the decision problem Total Dominating Set is to decide whether `G`
has a total dominating set of size at most `k`. We prove that Total Dominating Set is
NP-complete on (i) 2-degenerate planar perfect elimination bipartite graphs of maximum degree
three". Those graphs are bipartite, so their result gives NP-hardness on bipartite graphs.

This is the restriction of TOTAL DOMINATING SET (`TotalDominatingSetWanted`) to bipartite graphs.
The instance type, the graph, the well-formedness (a simple edge list on `Fin n`) and the question
are the parent's (`TotalDominatingSet.TotalDominatingSetInstance`, `TotalDominatingSet.Graph`,
`TotalDominatingSet.WellFormed`, `TotalDominatingSet.TotalDominatingSetFeasible`); `WellFormed` adds
the bound `0 < K ≤ |V|` of Shalu and Kirubakaran, no isolated vertex (every vertex has a neighbor; a
graph with an isolated vertex has no total dominating set;
`TotalDominatingSetUndirectedPathGraphsWanted` adds the same condition), and the class: Mathlib's
`SimpleGraph.IsBipartite` (a proper 2-coloring exists). Without isolated vertices `n ≤ 2|E|`, so the
binary vertex count does not make the encoding succinct. Membership in NP takes `D` as the
certificate; bipartiteness is checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`),
`0 < K ≤ |V| = n`, no isolated vertex, and the graph is bipartite. -/
def WellFormed (i : TotalDominatingSetInstance) : Prop :=
  TotalDominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧
    (∀ v : Fin i.1, ∃ u, (Graph i).Adj v u) ∧ (Graph i).IsBipartite

open Classical in
/-- TOTAL DOMINATING SET on bipartite graphs as a decision problem over bitstrings. -/
noncomputable def totalDominatingSetBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TotalDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ TotalDominatingSetFeasible i)
  | none => false

/-- **TOTAL DOMINATING SET on bipartite graphs is NP-complete.** Source: Pfaff, Laskar and
Hedetniemi (1983); Shalu and Kirubakaran (2025). -/
public theorem_wanted totalDominatingSetBipartite_npComplete :
    totalDominatingSetBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalDominatingSetBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.TotalDominatingSetBipartite
