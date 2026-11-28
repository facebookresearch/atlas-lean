/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND5] CAPACITATED SPANNING TREE;
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CapacitatedSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree

/-!
# CAPACITATED SPANNING TREE is NP-complete

INSTANCE: a graph `G = (V, E)`, a specified vertex `v₀ ∈ V`, a capacity `c(e) ∈ ℤ₀⁺` and a
length `l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a requirement `r(v) ∈ ℤ₀⁺` for each `v ∈ V - {v₀}`, and a
bound `B ∈ ℤ₀⁺`. QUESTION: is there a spanning tree `T` for `G` such that the sum of the lengths
of the edges in `T` does not exceed `B` and such that for each edge `e` in `T`, if `U(e)` is the
set of vertices whose path to `v₀` in `T` contains `e`, then `∑_{u ∈ U(e)} r(u) ≤ c(e)`?

A spanning tree of `G` is a Mathlib `SimpleGraph` `T` on the vertices of `G` with `T ≤ G` and
`T.IsTree`, the form of Mathlib's `SimpleGraph.Connected.exists_isTree_le`. The path from `u`
to `v₀` in `T` is a `SimpleGraph.Walk` with `SimpleGraph.Walk.IsPath`; it is unique in a tree,
so `u ∈ U(e)` is stated as "some path from `u` to `v₀` in `T` contains `e`". The requirement
list has one entry per vertex; the entry of `v₀` is never read, since `v₀ ∉ U(e)` (its path to
itself has no edges).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CAPACITATED SPANNING TREE is NP-complete.** Source: Garey and Johnson (1979), [ND5];
Papadimitriou (1978). -/
public theorem_wanted capacitatedSpanningTree_npComplete :
    capacitatedSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L capacitatedSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree
