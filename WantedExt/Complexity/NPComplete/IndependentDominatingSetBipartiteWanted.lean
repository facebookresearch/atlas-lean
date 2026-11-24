/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET on bipartite graphs is NP-complete

Source:
D. G. Corneil and Y. Perl, "Clustering and domination in perfect graphs", Discrete Applied
Mathematics 9(1) (1984), 27-39, doi:10.1016/0166-218X(84)90088-X;
ISGCI, Information System on Graph Classes and their Inclusions, class bipartite (gc_69,
https://www.graphclasses.org/classes/gc_69.html), problem Independent dominating set;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DominatingSetBipartiteWanted
public import WantedExt.Complexity.NPComplete.IndependentDominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetBipartite

open MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSet

/-!
# INDEPENDENT DOMINATING SET on bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` and a positive integer `K`.

QUESTION: is there a set `V' ⊆ V` with `|V'| ≤ K` that is independent (no two vertices of `V'`
are adjacent) and dominating (every vertex not in `V'` has a neighbor in `V'`), equivalently a
maximal independent set of size at most `K`?

Corneil and Perl (1984, abstract): "it is shown that [...] the independent k-dominating set
problem is NP-complete for bipartite graphs". ISGCI lists Independent dominating set ("a set S of
pairwise non-adjacent vertices, with |S| <= k, such that every vertex in G is either in S or
adjacent to a vertex in S") as NP-complete on bipartite graphs.

The instance and the question are those of
`WantedExt.Complexity.NPComplete.IndependentDominatingSetWanted` (a simple graph on `Fin n`
given by an edge list, and the bound `K`; `IndependentDominatingSetFeasible`: a set of at most
`K` vertices that dominates every vertex and contains no edge). The instance class is exactly
that of `WantedExt.Complexity.NPComplete.DominatingSetBipartiteWanted`, whose
`DominatingSetBipartite.WellFormed` is used as is: the simple-edge-list condition, the graph
bipartite as Mathlib's `SimpleGraph.IsBipartite`, and `0 < K`. Both modules use the instance
type `ℕ × List (ℕ × ℕ) × ℕ` and the graph `Cslib.Complexity.Karp.edgeGraph n E`, so
`DominatingSet.Graph i` and `IndependentDominatingSet.Graph i` are the same graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- INDEPENDENT DOMINATING SET on bipartite graphs as a decision problem over bitstrings. -/
noncomputable def independentDominatingSetBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentDominatingSetInstance) x with
  | some i => decide (DominatingSetBipartite.WellFormed i ∧ IndependentDominatingSetFeasible i)
  | none => false

/-- **INDEPENDENT DOMINATING SET on bipartite graphs is NP-complete.** Source: Corneil and Perl
(1984); ISGCI (gc_69). -/
public theorem_wanted independentDominatingSetBipartite_npComplete :
    independentDominatingSetBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentDominatingSetBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetBipartite
