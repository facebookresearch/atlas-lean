/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BRIDGE-CONNECTIVITY AUGMENTATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND18] BICONNECTIVITY
AUGMENTATION, p. 210, comment: "The related problem in which G' must be bridge connected,
i.e., cannot be disconnected by removing a single edge, is also NP-complete";
K. P. Eswaran and R. E. Tarjan, "Augmentation problems", SIAM Journal on Computing 5 (1976),
653-665, doi:10.1137/0205044.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BridgeConnectivityAugmentationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BridgeConnectivityAugmentation

/-!
# BRIDGE-CONNECTIVITY AUGMENTATION is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w({u, v}) ∈ ℤ⁺` for each unordered pair `{u, v}` of
vertices from `V`, and a positive integer `B`. QUESTION: is there a set `E'` of unordered pairs
of vertices from `V` such that `∑_{e ∈ E'} w(e) ≤ B` and the graph `G' = (V, E ∪ E')` is bridge
connected, i.e., cannot be disconnected by removing a single edge?

The instance format and the weight lookup are those of BICONNECTIVITY AUGMENTATION
(`MetaMathlibExt.Complexity.NPComplete.BiconnectivityAugmentation`): vertices
`0, ..., n - 1`, the edge list of `G`, an `n × n` symmetric weight matrix with positive
off-diagonal entries (the diagonal is never used), and `B`. Here `V` only has to be nonempty
(`n ≥ 1`), not of size at least 3. Bridge connectivity is Mathlib's
`SimpleGraph.IsEdgeConnected 2`: every two vertices stay joined by a walk after deleting any
single edge; on a nonempty vertex set this says that `G'` is connected and has no bridge.
`E'` is a list of pairs of distinct vertices; listing a pair twice only adds its weight twice.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BRIDGE-CONNECTIVITY AUGMENTATION is NP-complete.** Source: Garey and Johnson (1979),
[ND18], comment; Eswaran and Tarjan (1976). -/
public theorem_wanted bridgeConnectivityAugmentation_npComplete :
    bridgeConnectivityAugmentationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bridgeConnectivityAugmentationDec

end MetaMathlibExt.Complexity.NPComplete.BridgeConnectivityAugmentation
