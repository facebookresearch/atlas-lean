/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ODD HOLE THROUGH A GIVEN VERTEX is NP-complete

Source:
D. Bienstock, "On the complexity of testing for odd holes and induced odd paths", Discrete
Mathematics 90 (1991), 85-92, doi:10.1016/0012-365X(91)90098-M, and "Corrigendum", Discrete
Mathematics 102 (1992), 109;
M. Chudnovsky, A. Scott, P. Seymour and S. Spirkl, "Detecting an odd hole", Journal of the ACM
67 (2020), Article 5, doi:10.1145/3375720 (arXiv:1903.00208; Section 1: "D. Bienstock [2, 3]
showed that testing if a graph has an odd hole containing a given vertex is NP-complete").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OddHoleThroughVertexDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OddHoleThroughVertex

/-!
# ODD HOLE THROUGH A GIVEN VERTEX is NP-complete

INSTANCE: a graph `G = (V, E)` and a vertex `v ∈ V`. QUESTION: does `G` have an odd hole
containing `v`, i.e., an induced cycle of odd length at least `5` through `v`?

Chudnovsky, Scott, Seymour and Spirkl (Section 1): "A hole of `G` is an induced subgraph of `G`
that is a cycle of length at least four", and "D. Bienstock [2, 3] showed that testing if a graph
has an odd hole containing a given vertex is NP-complete" (in contrast, they show that testing
for an odd hole anywhere in the graph is polynomial).

A hole of length `k` is an induced copy of Mathlib's `SimpleGraph.cycleGraph k`: a graph
embedding `cycleGraph k ↪g G` (`SimpleGraph.Embedding`, an injective map that preserves and
reflects adjacency, so the copy is induced, i.e. chordless). The hole is odd when `k` is odd, and
it contains `v` when `v` is the image of one of its vertices. The given vertex is a natural number
`v < n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ODD HOLE THROUGH A GIVEN VERTEX is NP-complete.** Source: Bienstock (1991, 1992);
Chudnovsky, Scott, Seymour and Spirkl (2020), Section 1. -/
public theorem_wanted oddHoleThroughVertex_npComplete :
    oddHoleThroughVertexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oddHoleThroughVertexDec

end MetaMathlibExt.Complexity.NPComplete.OddHoleThroughVertex
