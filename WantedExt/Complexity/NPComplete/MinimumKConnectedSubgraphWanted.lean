/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM K-CONNECTED SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT31] MINIMUM K-CONNECTED
SUBGRAPH; R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT, the case `K = 2`, `B = |V|`);
S. Khuller and U. Vishkin, "Biconnectivity approximations and graph carvings", Journal of
the ACM 41 (1994), 214-235, doi:10.1145/174652.174654.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumKConnectedSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumKConnectedSubgraph

/-!
# MINIMUM K-CONNECTED SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and positive integers `K ≤ |V|` and `B ≤ |E|`. QUESTION: is
there a subset `E' ⊆ E` with `|E'| ≤ B` such that `G' = (V, E')` is `K`-connected, i.e.,
cannot be disconnected by removing fewer than `K` vertices?

The subset `E'` is a spanning subgraph `H ≤ G` and `|E'|` is `H.edgeSet.ncard`. "Cannot be
disconnected by removing fewer than `K` vertices" says that for every vertex set `S` with
`|S| < K` the subgraph of `H` induced on the remaining vertices is connected (since
`K ≤ |V|`, at least one vertex remains). This is the second conjunct of
`SimpleGraph.IsVertexConnected K H` (`MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity`),
which also requires `K < |V|`. The two agree for `K < |V|`; at the bound `K = |V|` that
Garey and Johnson admit, their wording accepts the complete graph, while
`IsVertexConnected |V|` holds for no graph, so the condition is stated as Garey and Johnson
word it. Under `WellFormed` the edge list has one entry per edge, so its length is `|E|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM K-CONNECTED SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979),
[GT31]; Karp (1972); Khuller and Vishkin (1994). -/
public theorem_wanted minimumKConnectedSubgraph_npComplete :
    minimumKConnectedSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumKConnectedSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.MinimumKConnectedSubgraph
