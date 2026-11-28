/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-CAPACITATED TREE PARTITION is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MINIMUM K-CAPACITATED TREE PARTITION;
C. Imielińska, B. Kalantari and L. Khachiyan, "A greedy heuristic for a minimum-weight forest
problem", Operations Research Letters 14 (1993), 65-71, doi:10.1016/0167-6377(93)90097-Z
(NP-complete for every fixed `k ≥ 4`; not available to us, result as recorded by Goemans and
Williamson);
M. X. Goemans and D. P. Williamson, "A general approximation technique for constrained forest
problems", SIAM Journal on Computing 24 (1995), 296-317, doi:10.1137/S0097539793242618
(lower capacitated tree partitioning).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KCapacitatedTreePartitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KCapacitatedTreePartition

open BoundedDiameterSpanningTree (BoundedDiameterSpanningTreeInstance endpoints)

/-!
# k-CAPACITATED TREE PARTITION is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight function `w : E → ℕ`, a positive integer `k`, and a
positive integer `K`. QUESTION: is there a `k`-capacitated tree partition of `G`, i.e. a
collection of vertex-disjoint edge sets `E₁, …, E_m ⊆ E` covering the vertices, each forming a
tree with at least `k` vertices, of total weight `∑ᵢ ∑_{e ∈ Eᵢ} w(e)` at most `K`?

This is the decision version of MINIMUM K-CAPACITATED TREE PARTITION in the compendium of
Crescenzi and Kann, the lower capacitated tree partitioning problem of Goemans and Williamson
("vertex-disjoint trees ... that cover all vertices", each with at least `k` vertices).

The instance reuses the type of `BoundedDiameterSpanningTreeWanted` (vertex count `n`, edge list
of triples `(u, v, w)`, two numbers, here `k` and `K`). The union `F` of `E₁, …, E_m` is a
sublist of the edge list (a choice of edges, since the list has no repeated edge); the graph
`forest i F` on all of `V` with the edges of `F` is acyclic (a forest), its connected components
are the trees, each component has at least `k` vertices, and the weight is the sum of `w` over
`F`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **k-CAPACITATED TREE PARTITION is NP-complete.** Source: Crescenzi and Kann, MINIMUM
K-CAPACITATED TREE PARTITION; Imielińska, Kalantari and Khachiyan (1993), as recorded by Goemans
and Williamson (1995). -/
public theorem_wanted kCapacitatedTreePartition_npComplete :
    kCapacitatedTreePartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kCapacitatedTreePartitionDec

end MetaMathlibExt.Complexity.NPComplete.KCapacitatedTreePartition
