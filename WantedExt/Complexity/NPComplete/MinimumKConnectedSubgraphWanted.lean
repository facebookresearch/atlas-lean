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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card

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

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, connectivity `K`, edge
budget `B`. -/
abbrev MinimumKConnectedSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinimumKConnectedSubgraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `0 < K ≤ |V|`, and
`0 < B ≤ |E|`, the length of the edge list. -/
def WellFormed (i : MinimumKConnectedSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2.1 ∧ i.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2 ∧ i.2.2.2 ≤ i.2.1.length

/-- Some spanning subgraph `H ≤ G` has at most `B` edges and stays connected after removing
any set of fewer than `K` vertices. -/
def MinimumKConnectedSubgraphFeasible (i : MinimumKConnectedSubgraphInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H ≤ Graph i ∧ H.edgeSet.ncard ≤ i.2.2.2 ∧
    ∀ S : Finset (Fin i.1), S.card < i.2.2.1 →
      (H.induce (S : Set (Fin i.1))ᶜ).Connected

open Classical in
/-- MINIMUM K-CONNECTED SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def minimumKConnectedSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumKConnectedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ MinimumKConnectedSubgraphFeasible i)
  | none => false

/-- **MINIMUM K-CONNECTED SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979),
[GT31]; Karp (1972); Khuller and Vishkin (1994). -/
public theorem_wanted minimumKConnectedSubgraph_npComplete :
    minimumKConnectedSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumKConnectedSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.MinimumKConnectedSubgraph
