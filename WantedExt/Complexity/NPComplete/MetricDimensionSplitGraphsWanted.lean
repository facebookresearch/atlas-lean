/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC DIMENSION for split graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT61] METRIC DIMENSION;
L. Epstein, A. Levin and G. J. Woeginger, "The (weighted) metric dimension of graphs: hard and
easy cases", Algorithmica 72 (2015), 1130-1171, doi:10.1007/s00453-014-9896-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MetricDimensionSplitGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricDimensionSplitGraphs

/-!
# METRIC DIMENSION for split graphs is NP-complete

INSTANCE: a connected split graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is
there a subset `V' ⊆ V` with `|V'| ≤ K` such that for each pair `u, v` of distinct vertices
there is a vertex `w ∈ V'` with `d(u, w) ≠ d(w, v)`?

This is the restriction of METRIC DIMENSION ([GT61], `MetricDimensionWanted`) to split graphs,
the graphs whose vertex set splits into a clique and an independent set
(`DominatingSetSplitGraphs.IsSplitGraph`). The instance type and the question are the parent's
(`MetricDimension.MetricDimensionInstance`, `MetricDimension.MetricDimensionFeasible`, with
Mathlib's `SimpleGraph.dist`); `WellFormed` is the parent's (a simple edge list, a connected
graph, `0 < K ≤ |V|`) plus the restriction.

Epstein, Levin and Woeginger (abstract): "for split graphs, bipartite graphs, co-bipartite
graphs, and line graphs of bipartite graphs, the problem of computing the unweighted metric
dimension of the graph is NP-hard". Membership in NP is the parent's: a set `V'` is a
certificate, checked with polynomial-time distance computations.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **METRIC DIMENSION for split graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT61]; Epstein, Levin and Woeginger (2015). -/
public theorem_wanted metricDimensionSplitGraphs_npComplete :
    metricDimensionSplitGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricDimensionSplitGraphsDec

end MetaMathlibExt.Complexity.NPComplete.MetricDimensionSplitGraphs
