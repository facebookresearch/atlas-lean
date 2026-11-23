/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM K-EDGE-CONNECTED SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT31] MINIMUM K-CONNECTED SUBGRAPH,
comment ("Corresponding edge-connectivity problem is also NP-complete"), credited to F. R. K. Chung
and R. L. Graham (1977, private communication);
S. Khuller and U. Vishkin, "Biconnectivity approximations and graph carvings", Journal of the ACM
41 (1994), 214-235, doi:10.1145/174652.174654.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import WantedExt.Complexity.NPComplete.MinimumKConnectedSubgraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumKEdgeConnectedSubgraph

open MinimumKConnectedSubgraph (MinimumKConnectedSubgraphInstance Graph WellFormed)

/-!
# MINIMUM K-EDGE-CONNECTED SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and positive integers `K ≤ |V|` and `B ≤ |E|`.
QUESTION: is there a subset `E' ⊆ E` with `|E'| ≤ B` such that `G' = (V, E')` is
`K`-edge-connected, i.e., cannot be disconnected by removing fewer than `K` edges?

Garey and Johnson state MINIMUM K-CONNECTED SUBGRAPH ([GT31], vertex connectivity,
`MinimumKConnectedSubgraphWanted`) and record in its comment that the "corresponding
edge-connectivity problem is also NP-complete", crediting Chung and Graham (1977, private
communication; the original was not available). Khuller and Vishkin record that finding a
smallest 2-edge-connected spanning subgraph is NP-hard. Hardness also follows directly from
HAMILTONIAN CIRCUIT (Karp 1972) with `K = 2` and `B = |V|`: a 2-edge-connected spanning
subgraph of a graph with at least three vertices has minimum degree at least 2, hence at least
`|V|` edges, and with exactly `|V|` edges it is connected and 2-regular, i.e., a Hamiltonian
circuit. A spanning subgraph is a polynomial certificate and edge connectivity is decidable in
polynomial time (maximum flow), so the problem is in NP.

The instance, the graph and the well-formedness are those of MINIMUM K-CONNECTED SUBGRAPH
(`MinimumKConnectedSubgraph.MinimumKConnectedSubgraphInstance`,
`MinimumKConnectedSubgraph.Graph`, `MinimumKConnectedSubgraph.WellFormed`: a simple edge list
on the vertices `0, ..., n - 1`, `0 < K ≤ |V|` and `0 < B ≤ |E|`, the length of the edge list),
reused unchanged; Garey and Johnson give the edge-connectivity variant no separate instance
class, so it keeps the bound `K ≤ |V|` of [GT31]. The subset `E'` is a spanning subgraph
`H ≤ G` and `|E'|` is `H.edgeSet.ncard`. "Cannot be disconnected by removing fewer than `K`
edges" is Mathlib's `SimpleGraph.IsEdgeConnected K H`: any two vertices remain reachable after
deleting any set of fewer than `K` edges. Since `0 < K` it includes that `H` is connected
(deleting no edges), and `K ≤ |V|` makes `V` nonempty.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some spanning subgraph `H ≤ G` has at most `B` edges and is `K`-edge-connected: any two
vertices stay reachable after deleting any set of fewer than `K` edges. -/
def MinimumKEdgeConnectedSubgraphFeasible (i : MinimumKConnectedSubgraphInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H ≤ Graph i ∧ H.edgeSet.ncard ≤ i.2.2.2 ∧
    H.IsEdgeConnected (i.2.2.1 : ℕ∞)

open Classical in
/-- MINIMUM K-EDGE-CONNECTED SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def minimumKEdgeConnectedSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumKConnectedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ MinimumKEdgeConnectedSubgraphFeasible i)
  | none => false

/-- **MINIMUM K-EDGE-CONNECTED SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979),
[GT31]; Khuller and Vishkin (1994). -/
public theorem_wanted minimumKEdgeConnectedSubgraph_npComplete :
    minimumKEdgeConnectedSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumKEdgeConnectedSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.MinimumKEdgeConnectedSubgraph
