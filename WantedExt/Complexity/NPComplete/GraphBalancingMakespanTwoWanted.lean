/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH BALANCING (makespan 2, weights 1 and 2) is NP-complete

Source:
T. Ebenlendr, M. Krčál, and J. Sgall, "Graph balancing: a special case of scheduling unrelated
parallel machines", Algorithmica 68 (2014), 62-80, doi:10.1007/s00453-012-9668-9 (the problem);
Y. Asahiro, E. Miyano, and H. Ono, "Graph classes and the complexity of the graph orientation
minimizing the maximum weighted outdegree", Discrete Applied Mathematics 159 (2011), 498-508,
doi:10.1016/j.dam.2010.11.003, Theorem 13 with `k = 2`.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphBalancingMakespanTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphBalancingMakespanTwo

/-!
# GRAPH BALANCING (makespan 2, weights 1 and 2) is NP-complete

INSTANCE: an undirected multigraph `G = (V, E)` (parallel edges and loops allowed) with a weight
`w(e) ∈ {1, 2}` on each edge. QUESTION: can the edges be oriented so that the load of every
vertex, the total weight of the edges oriented toward it, is at most `2`?

This is the decision version, at makespan `2`, of GRAPH BALANCING of Ebenlendr, Krčál, and
Sgall: scheduling with restricted assignment where every job (edge) can run on one of at most
two machines (its endpoints; a loop is a job fixed to one machine), with weights `1` and `2`.
Ebenlendr et al. record that approximating GRAPH BALANCING within a ratio below `3/2` is
NP-hard. Asahiro, Miyano, and Ono (2011, Theorem 13 with `k = 2`) prove the decision problem
itself strongly NP-hard: deciding whether a simple planar bipartite graph with edge weights in
`{1, 2}` has an orientation of maximum weighted outdegree at most `2`. Reversing every edge
turns outdegree into load, and simple graphs are multigraphs. The bound `2` is part of the
problem.

Vertices are `0, …, n - 1`. An edge is an entry `(u, v, w)` of the edge list: endpoints `u` and
`v` (`u = v` for a loop) and weight `w`; repeated entries are parallel edges. An orientation
chooses one endpoint of each entry, its head.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH BALANCING (makespan 2, weights 1 and 2) is NP-complete.** Source: Ebenlendr, Krčál,
and Sgall (2014); Asahiro, Miyano, and Ono (2011), Theorem 13. -/
public theorem_wanted graphBalancingMakespanTwo_npComplete :
    graphBalancingMakespanTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphBalancingMakespanTwoDec

end MetaMathlibExt.Complexity.NPComplete.GraphBalancingMakespanTwo
