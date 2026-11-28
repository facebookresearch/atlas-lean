/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMUM COMMUNICATION SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND7] OPTIMUM COMMUNICATION
SPANNING TREE;
D. S. Johnson, J. K. Lenstra and A. H. G. Rinnooy Kan, "The complexity of the network design
problem", Networks 8(4) (1978), 279-285, doi:10.1002/net.3230080402;
T. C. Hu, "Optimum communication spanning trees", SIAM Journal on Computing 3(3) (1974),
188-195, doi:10.1137/0203015 (the problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OptimumCommunicationSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTree

/-!
# OPTIMUM COMMUNICATION SPANNING TREE is NP-complete

An instance is the complete graph on a vertex set `V`, a weight `w(e) ∈ ℕ` for each edge `e`,
a requirement `r({u, v}) ∈ ℕ` for each pair of vertices, and a bound `B ∈ ℕ`. The question is
whether there is a spanning tree `T` of the complete graph such that
`∑_{u, v ∈ V} W_T({u, v}) * r({u, v}) ≤ B`, where `W_T({u, v})` is the sum of the weights of
the edges on the path joining `u` and `v` in `T`.

Every tree on `V` is a spanning tree of the complete graph on `V`, so `T` ranges over all trees
on `Fin n`. A tree has exactly one path between any two vertices (Mathlib
`SimpleGraph.IsTree.existsUnique_path`), so choosing a path for every ordered pair, as the
statement does, fixes `W_T`. Weights and requirements are data on unordered pairs, so the sum
counts each unordered pair `{u, v}` of distinct vertices once, as `u < v` (pairs `u = v`
contribute nothing: the path from `u` to itself is empty). Weights and requirements are given
by symmetric `n × n` matrices with zero diagonal, the encoding of functions on unordered pairs
of distinct vertices. Numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **OPTIMUM COMMUNICATION SPANNING TREE is NP-complete.** Source: Garey and Johnson (1979),
[ND7]; Johnson, Lenstra and Rinnooy Kan (1978). -/
public theorem_wanted optimumCommunicationSpanningTree_npComplete :
    optimumCommunicationSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimumCommunicationSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTree
