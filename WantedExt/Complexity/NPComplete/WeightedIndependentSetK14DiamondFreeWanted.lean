/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED INDEPENDENT SET on (K_1,4, diamond)-free graphs is NP-complete

Source:
D. G. Corneil, "The complexity of generalized clique packing", Discrete Applied Mathematics 12
(1985), 233-239, doi:10.1016/0166-218X(85)90027-7;
A. Brandstädt, V. B. Le and S. Mahfud, "New applications of clique separator decomposition for
the Maximum Weight Stable Set problem", Theoretical Computer Science 370 (2007), 229-239,
doi:10.1016/j.tcs.2006.10.035 (records the attribution: the maximum weight stable set problem
"remains NP-complete even on very restricted instances such as ... (K1,4,diamond)-free graphs",
citing Corneil (1985)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeightedIndependentSetK14DiamondFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedIndependentSetK14DiamondFree

/-!
# WEIGHTED INDEPENDENT SET on (K_1,4, diamond)-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` with no induced subgraph isomorphic to the star `K_1,4` (a vertex
with four pairwise non-adjacent neighbours) and no induced subgraph isomorphic to the diamond
(`K_4` minus an edge), a weight `w(v)` for each vertex `v`, and a number `k`.
QUESTION: does `G` contain a set `S` of pairwise non-adjacent vertices with total weight
`∑_{v ∈ S} w(v) ≥ k`?

This is ISGCI's problem "Weighted independent set" on the class `(K_1,4, diamond)`-free
(`gc_413`): "Input: A graph `G` in this class with weight function on the vertices and a real
`k`. Output: True iff `G` contains a set `S` of pairwise non-adjacent vertices, such that the
sum of the weights of the vertices in `S` is at least `k`." ISGCI records it as NP-complete,
citing Corneil (1985).

The graph is given by an edge list on `Fin n` (`Cslib.Complexity.Karp.edgeGraph`), the weights
by a list of length `n` (the weight of vertex `v` is its `v`-th entry), and the question asks for
a `Finset` of vertices whose coercion is Mathlib's `SimpleGraph.IsIndepSet`. "Free" means no
induced subgraph isomorphic to the forbidden graph: Mathlib's `SimpleGraph.IsIndContained` (an
induced embedding) with the star `completeBipartiteGraph (Fin 1) (Fin 4)`, as in
`IndependentSetK14FreeWanted`, and with the diamond `ColoringK4ClawDiamondFree.diamond` from
`ColoringK4ClawDiamondFreeWanted` (`K_4` on `Fin 4` minus the edge `{0, 1}`), reused unchanged.

Weights and `k` are natural numbers in the canonical binary encoding. ISGCI states real
weights; a finite encoding gives rational weights, which scale to integers by a common
denominator, and a vertex of negative weight can be deleted (removing it from an independent set
keeps the set independent and does not lower its weight, and the class is closed under induced
subgraphs). With every weight `1` the question is INDEPENDENT SET on the same class.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WEIGHTED INDEPENDENT SET on `(K_1,4, diamond)`-free graphs is NP-complete.** Source:
Corneil (1985); Brandstädt, Le and Mahfud (2007); ISGCI (`gc_413`). -/
public theorem_wanted weightedIndependentSetK14DiamondFree_npComplete :
    weightedIndependentSetK14DiamondFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedIndependentSetK14DiamondFreeDec

end MetaMathlibExt.Complexity.NPComplete.WeightedIndependentSetK14DiamondFree
