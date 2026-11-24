/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM K-CONNECTED SUBGRAPH for fixed K ≥ 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT31] MINIMUM K-CONNECTED
SUBGRAPH, p. 198 (comment: "Both problems remain NP-complete for any fixed K ≥ 2 and can be
solved trivially in polynomial time for K = 1"; reference: Chung and Graham, 1977).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumKConnectedSubgraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumKConnectedSubgraphFixedK

/-!
# MINIMUM K-CONNECTED SUBGRAPH for fixed K ≥ 2 is NP-complete

For a fixed integer `K ≥ 2`:

INSTANCE: a graph `G = (V, E)` and a positive integer `B ≤ |E|`.
QUESTION: is there a subset `E' ⊆ E` with `|E'| ≤ B` such that `G' = (V, E')` is
`K`-connected, i.e., cannot be disconnected by removing fewer than `K` vertices?

This is MINIMUM K-CONNECTED SUBGRAPH ([GT31], `MinimumKConnectedSubgraphWanted`, the vertex-
connectivity problem) with the connectivity `K` fixed instead of part of the instance. An
instance is `(n, E, B)`; it is decided as the [GT31] instance `(n, E, K, B)` (`withK K`), whose
`MinimumKConnectedSubgraph.WellFormed` (simple edge list, `0 < K ≤ |V|`, `0 < B ≤ |E|`) and
`MinimumKConnectedSubgraph.MinimumKConnectedSubgraphFeasible` are reused unchanged; so graphs
with fewer than `K` vertices are malformed, as Garey and Johnson's `K ≤ |V|` makes them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, edge budget `B`; the
connectivity `K` is fixed. -/
abbrev MinimumKConnectedSubgraphFixedKInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The [GT31] instance `(n, E, K, B)` of an instance `(n, E, B)` and the fixed `K`. -/
def withK (K : ℕ) (i : MinimumKConnectedSubgraphFixedKInstance) :
    MinimumKConnectedSubgraph.MinimumKConnectedSubgraphInstance :=
  (i.1, i.2.1, K, i.2.2)

open Classical in
/-- MINIMUM K-CONNECTED SUBGRAPH for a fixed `K` as a decision problem over bitstrings. -/
noncomputable def minimumKConnectedSubgraphFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumKConnectedSubgraphFixedKInstance) x with
  | some i => decide (MinimumKConnectedSubgraph.WellFormed (withK K i) ∧
      MinimumKConnectedSubgraph.MinimumKConnectedSubgraphFeasible (withK K i))
  | none => false

/-- **MINIMUM K-CONNECTED SUBGRAPH is NP-complete for every fixed `K ≥ 2`.** Source: Garey and
Johnson (1979), [GT31], comment (Chung and Graham, 1977). -/
public theorem_wanted minimumKConnectedSubgraphFixedK_npComplete (K : ℕ) (hK : 2 ≤ K) :
    minimumKConnectedSubgraphFixedKDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (minimumKConnectedSubgraphFixedKDec K)

end MetaMathlibExt.Complexity.NPComplete.MinimumKConnectedSubgraphFixedK
