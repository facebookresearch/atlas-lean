/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHORDAL EDGE DELETION is NP-complete

Source:
A. Natanzon, R. Shamir and R. Sharan, "Complexity classification of some edge modification
problems", Discrete Applied Mathematics 113 (2001), 109-128,
doi:10.1016/S0166-218X(00)00391-7, Theorem 3.6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChordalEdgeDeletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChordalEdgeDeletion

/-!
# CHORDAL EDGE DELETION is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) and a nonnegative integer `K`.
QUESTION: can `G` be made chordal by deleting at most `K` edges, i.e., is there a set `F ⊆ E`
with `|F| ≤ K` such that `(V, E \ F)` is chordal?

Natanzon, Shamir and Sharan call a graph chordal if it contains no induced cycle of length
greater than `3`, and prove CHORDAL DELETION NP-complete (Theorem 3.6). The graph after the
deletion is a `SimpleGraph` `H` on the same vertices with `H ≤ G`; the deleted edges are
`G.edgeSet \ H.edgeSet`, as in `ClusterDeletionWanted`. Chordality is stated as in
`DominatingSetChordalGraphsWanted` and `HamiltonianCircuitChordalGraphsWanted`: no cycle graph
`Cₖ` with `k ≥ 4` is an induced subgraph (Mathlib's `SimpleGraph.cycleGraph` and
`SimpleGraph.IsIndContained`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CHORDAL EDGE DELETION is NP-complete.** Source: Natanzon, Shamir and Sharan (2001),
Theorem 3.6. -/
public theorem_wanted chordalEdgeDeletion_npComplete :
    chordalEdgeDeletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chordalEdgeDeletionDec

end MetaMathlibExt.Complexity.NPComplete.ChordalEdgeDeletion
