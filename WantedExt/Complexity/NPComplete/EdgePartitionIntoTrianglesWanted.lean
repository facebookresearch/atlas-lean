/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE PARTITION INTO TRIANGLES is NP-complete

Source:
I. Holyer, "The NP-completeness of some edge-partition problems", SIAM Journal on Computing
10(4) (1981), 713-717, doi:10.1137/0210054 (for each fixed `n ≥ 3` it is NP-complete to
determine whether an arbitrary graph can be edge-partitioned into subgraphs isomorphic to the
complete graph `K_n`; here `n = 3`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EdgePartitionIntoTrianglesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgePartitionIntoTriangles

/-!
# EDGE PARTITION INTO TRIANGLES is NP-complete

INSTANCE: a graph `G = (V, E)`.
QUESTION: can `G` be edge-partitioned into subgraphs isomorphic to the complete graph `K₃`, that
is, is there a collection of triangles of `G` such that every edge of `G` lies in exactly one of
them?

A triangle of `G` is a set of three vertices that is a clique, Mathlib's
`SimpleGraph.IsNClique 3`; its subgraph is the `K₃` on those vertices, and an edge `uv` lies in
it when both `u` and `v` do. Every edge of every chosen triangle is an edge of `G`, so covering
each edge of `G` exactly once is an edge partition.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EDGE PARTITION INTO TRIANGLES is NP-complete.** Source: Holyer (1981). -/
public theorem_wanted edgePartitionIntoTriangles_npComplete :
    edgePartitionIntoTrianglesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgePartitionIntoTrianglesDec

end MetaMathlibExt.Complexity.NPComplete.EdgePartitionIntoTriangles
