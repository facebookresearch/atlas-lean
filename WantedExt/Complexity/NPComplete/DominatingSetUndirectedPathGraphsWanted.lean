/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for undirected path graphs is NP-complete

Source:
K. S. Booth and J. H. Johnson, "Dominating sets in chordal graphs", SIAM Journal on Computing
11(1) (1982), 191-199, doi:10.1137/0211015 (finding a minimum dominating set is NP-complete for
chordal graphs, "even when restricted to undirected path graphs");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphs

/-!
# DOMINATING SET for undirected path graphs is NP-complete

INSTANCE: an undirected path graph `G = (V, E)`, that is, the vertex intersection graph of a
family of paths in an undirected tree, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex not in `V'` is joined to at least one member of `V'`?

This is the restriction of DOMINATING SET ([GT2], `DominatingSetDefs`) to undirected path
graphs. The instance type, the graph and the question are the parent's
(`DominatingSet.DominatingSetInstance`, `DominatingSet.Graph`,
`DominatingSet.DominatingSetFeasible`); `WellFormed` is the parent's plus the restriction and
Garey and Johnson's bounds `0 < K ≤ |V|`. A graph on `Fin n` is an undirected path graph when
there are a finite tree `T` (Mathlib's `SimpleGraph.IsTree`) and, for each vertex `v`, the vertex
set `P v` of a path in `T` (a `SimpleGraph.Walk` with `IsPath`), such that two distinct vertices
are adjacent exactly when their paths share a vertex of `T`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DOMINATING SET for undirected path graphs is NP-complete.** Source: Booth and Johnson
(1982); Garey and Johnson (1979), [GT2]. -/
public theorem_wanted dominatingSetUndirectedPathGraphs_npComplete :
    dominatingSetUndirectedPathGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetUndirectedPathGraphsDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphs
