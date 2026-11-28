/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO ISOMORPHIC SUBGRAPHS (induced form) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 193, problem [GT12]
PARTITION INTO ISOMORPHIC SUBGRAPHS (main entry), credited there to
[Kirkpatrick and Hell, 1978], transformation from 3DM;
D. G. Kirkpatrick and P. Hell, "On the completeness of a generalized matching
problem", Proceedings of the 10th Annual ACM Symposium on Theory of Computing
(1978), 240-245, doi:10.1145/800133.804353.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoInducedIsomorphicSubgraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoInducedIsomorphicSubgraphs

/-!
# PARTITION INTO ISOMORPHIC SUBGRAPHS (induced form) is NP-complete

INSTANCE: graphs `G = (V, E)` and `H = (V', E')` with `|V| = q|V'|` for some positive integer
`q`. QUESTION: can the vertices of `G` be partitioned into `q` disjoint sets `V₁, ..., V_q` such
that, for `1 ≤ i ≤ q`, the subgraph of `G` induced by `Vᵢ` is isomorphic to `H`?

This is the main entry of Garey and Johnson's [GT12] (p. 193). The variant in the comment to that
entry, where `G[Vᵢ]` need only contain a spanning subgraph isomorphic to `H` (the `H`-factor
problem), is stated separately in
`WantedExt.Complexity.NPComplete.PartitionIntoIsomorphicSubgraphsWanted`. The two differ: the
triangle `K₃` has a spanning path on three vertices, but is not isomorphic to it.

The partition is a map `P : V → Fin q` with blocks `P⁻¹(k)`; "the subgraph of `G` induced by
`P⁻¹(k)` is isomorphic to `H`" is a graph isomorphism `H ≃g G[P⁻¹(k)]`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO ISOMORPHIC SUBGRAPHS, in Garey and Johnson's induced form, is
NP-complete.** Source: Garey and Johnson (1979), [GT12], p. 193; Kirkpatrick and Hell (1978). -/
public theorem_wanted partitionIntoInducedIsomorphicSubgraphs_npComplete :
    partitionIntoInducedIsomorphicSubgraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoInducedIsomorphicSubgraphsDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoInducedIsomorphicSubgraphs
