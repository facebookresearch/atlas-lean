/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISJOINT CONNECTING PATHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND40] DISJOINT
CONNECTING PATHS;
R. M. Karp, "On the computational complexity of combinatorial problems",
Networks 5 (1975), 45-68, doi:10.1002/net.1975.5.1.45;
J. F. Lynch, "The equivalence of theorem proving and the interconnection
problem", ACM SIGDA Newsletter 5 (1975), 31-36, doi:10.1145/1061425.1061430.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPaths

/-!
# DISJOINT CONNECTING PATHS is NP-complete

INSTANCE: a graph `G = (V, E)` and a collection of disjoint vertex pairs
`(s₁, t₁), (s₂, t₂), ..., (sₖ, tₖ)`. QUESTION: does `G` contain `k` mutually vertex-disjoint
paths, one connecting `sᵢ` and `tᵢ` for each `i`, `1 ≤ i ≤ k`?

The vertices are `0, ..., n - 1` and the graph is given by a simple edge list. The pairs are a
list of `k` pairs of vertices; "disjoint vertex pairs" means that the `2k` vertices
`s₁, t₁, ..., sₖ, tₖ` are pairwise distinct. A path connecting `sᵢ` and `tᵢ` is a Mathlib walk
`p : G.Walk u v` with `u = sᵢ`, `v = tᵢ` and `p.IsPath`; two paths are vertex-disjoint when
their vertex lists (`Walk.support`) are disjoint.

The directed version, with arbitrary source-target pairs, is
`WantedExt.Complexity.NPComplete.DirectedDisjointPathsWanted`; this module states the
undirected problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DISJOINT CONNECTING PATHS is NP-complete.** Source: Garey and Johnson (1979), [ND40];
Karp (1975); Lynch (1975). -/
public theorem_wanted disjointConnectingPaths_npComplete :
    disjointConnectingPathsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L disjointConnectingPathsDec

end MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPaths
