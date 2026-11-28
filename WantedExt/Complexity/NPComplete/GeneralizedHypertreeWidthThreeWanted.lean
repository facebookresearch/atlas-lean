/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED HYPERTREE WIDTH AT MOST 3 is NP-complete

Source:
G. Gottlob, Z. Miklós and T. Schwentick, "Generalized hypertree decompositions: NP-hardness and
tractable variants", Journal of the ACM 56 (2009), no. 6, 1-32, doi:10.1145/1568318.1568320;
W. Fischl, G. Gottlob and R. Pichler, "General and fractional hypertree decompositions: hard and
easy cases", Proceedings of the 37th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database
Systems (PODS 2018), 17-32, doi:10.1145/3196959.3196962 (arXiv:1611.01090), Section 1 (the
definition of generalized hypertree decompositions and width used below, and the attribution of
NP-completeness for `k = 3` to Gottlob, Miklós and Schwentick).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneralizedHypertreeWidthThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedHypertreeWidthThree

/-!
# GENERALIZED HYPERTREE WIDTH AT MOST 3 is NP-complete

INSTANCE: a hypergraph `H = (V(H), E(H))`. QUESTION: is the generalized hypertree width of `H` at
most 3, i.e., is there a generalized hypertree decomposition `⟨T, (B_u), (λ_u)⟩` of `H` of width
at most 3? Such a decomposition consists of a tree `T`, a bag `B_u ⊆ V(H)` and a function
`λ_u : E(H) → {0, 1}` for every node `u` of `T`, such that
(1) for each `e ∈ E(H)` there is a node `u` with `e ⊆ B_u`;
(2) for each `v ∈ V(H)` the set `{u | v ∈ B_u}` is connected in `T`;
(3) for each node `u`, `B_u ⊆ B(λ_u)`, the set of vertices covered by the hyperedges `e` with
`λ_u(e) = 1`;
and its width is the maximum over the nodes `u` of the number of hyperedges with `λ_u(e) = 1`.

Vertices are `Fin n` and hyperedges are the list positions `Fin m` of a list of vertex lists.
The tree is Mathlib's `SimpleGraph.IsTree` on `Fin N` nodes for some `N`; the source's trees are
rooted, but conditions (1)-(3) do not mention the root. `λ_u` is given by the set of hyperedges
it maps to 1. Condition (2) is Mathlib's `Preconnected` for the subgraph of `T` induced on
`{u | v ∈ B_u}`, so that the empty set counts as connected: a vertex in no hyperedge lies in no
bag, by (3). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED HYPERTREE WIDTH AT MOST 3 is NP-complete.** Source: Gottlob, Miklós and
Schwentick (2009); Fischl, Gottlob and Pichler (2018), Section 1. -/
public theorem_wanted generalizedHypertreeWidthThree_npComplete :
    generalizedHypertreeWidthThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalizedHypertreeWidthThreeDec

end MetaMathlibExt.Complexity.NPComplete.GeneralizedHypertreeWidthThree
