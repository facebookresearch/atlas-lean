/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for undirected path graphs is NP-complete

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Technical Report
RUU-CS-91-39, Department of Computer Science, Utrecht University (1991), abstract (SIMPLE MAX CUT
"is NP-complete when restricted to one of the following classes: chordal graphs, undirected path
graphs, split graphs, tripartite graphs, and graphs that are the complement of a bipartite
graph"); conference version STACS 94, LNCS 775 (1994), 769-780,
doi:10.1007/3-540-57785-8_189; journal version Nordic Journal of Computing 7(1) (2000), 14-31;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021,
Table 1 (MAX CUT on UNDIRECTED PATH graphs: N [20], [20] = Bodlaender and Jansen).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsWanted
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutUndirectedPathGraphs

open MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT for undirected path graphs is NP-complete

INSTANCE: an undirected path graph `G = (V, E)`, that is, the vertex intersection graph of a
family of paths in an undirected tree, and a positive integer `K`.
QUESTION: is there a partition of `V` into two sets with at least `K` edges between them?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one) restricted to undirected path graphs,
which Bodlaender and Jansen prove NP-complete. The instance, the simple-edge-list conditions and
the question are those of MAXIMUM CUT (`MaxCutDefs`, whose question counts edges), reused as in
`MaxCutSplitGraphsWanted`; the restriction adds to `WellFormed` that
`Cslib.Complexity.Karp.edgeGraph` is an undirected path graph, and `0 < K`.

"Undirected path graph" is the repository's predicate
`DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph` (also used by
`UndirectedPathGraphHamiltonianCircuitWanted`): for some finite tree `T` (Mathlib's
`SimpleGraph.IsTree`) each vertex `v` has the vertex set `P v` of a path in `T` (a
`SimpleGraph.Walk` with `IsPath`), and distinct vertices are adjacent exactly when their paths
share a vertex of `T`.

Membership in NP: a cut is a polynomial certificate, and undirected path graphs are recognized
in polynomial time (Gavril, "A recognition algorithm for the intersection graphs of paths in
trees", Discrete Mathematics 23 (1978), 211-227, doi:10.1016/0012-365X(78)90070-5). Vertices
outside the edge list are isolated; they change neither the answer nor membership in the class
(an isolated vertex takes a path consisting of a new leaf of `T`), so the check runs on the
non-isolated vertices and the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
`Fin n`) whose graph is an undirected path graph, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧
    DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph
      (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT for undirected path graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutUndirectedPathGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

/-- **SIMPLE MAX CUT for undirected path graphs is NP-complete.**
Source: Bodlaender and Jansen (1991; STACS 1994; Nordic J. Computing 2000). -/
public theorem_wanted simpleMaxCutUndirectedPathGraphs_npComplete :
    simpleMaxCutUndirectedPathGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutUndirectedPathGraphsDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutUndirectedPathGraphs
