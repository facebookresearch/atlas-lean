/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISJOINT CONNECTING PATHS for planar graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND40] DISJOINT CONNECTING PATHS,
p. 217, comment ("Remains NP-complete for planar graphs [Lynch, 1974], [Lynch, 1975]");
J. F. Lynch, "The equivalence of theorem proving and the interconnection problem", ACM SIGDA
Newsletter 5(3) (1975), 31-36, doi:10.1145/1061425.1061430.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DisjointConnectingPathsPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPathsPlanar

open DisjointConnectingPaths
  (DisjointConnectingPathsInstance Graph DisjointConnectingPathsFeasible)

/-!
# DISJOINT CONNECTING PATHS for planar graphs is NP-complete

INSTANCE: a planar graph `G = (V, E)` and a collection of disjoint vertex pairs
`(s₁, t₁), (s₂, t₂), ..., (sₖ, tₖ)`. QUESTION: does `G` contain `k` mutually vertex-disjoint
paths, one connecting `sᵢ` and `tᵢ` for each `i`, `1 ≤ i ≤ k`?

Garey and Johnson record in the comment to [ND40] that DISJOINT CONNECTING PATHS "remains
NP-complete for planar graphs", citing Lynch (1974, 1975); Lynch's 1975 paper reduces theorem
proving (satisfiability) to the wire-routing "interconnection problem". The paths are a
polynomial certificate and planarity is decidable in polynomial time, so the problem is in NP.

This is DISJOINT CONNECTING PATHS (`DisjointConnectingPathsWanted`) restricted to planar graphs.
The instance, the graph, the parent well-formedness (`DisjointConnectingPaths.WellFormed`: a
simple edge list on the vertices `0, ..., n - 1`, every `sᵢ` and `tᵢ` a vertex, and the `2k`
vertices `s₁, t₁, ..., sₖ, tₖ` pairwise distinct) and the question
(`DisjointConnectingPaths.DisjointConnectingPathsFeasible`) are the parent's, unchanged; the
restriction adds to `WellFormed` that the graph is planar. Planarity is MathlibExt's
`SimpleGraph.IsPlanar`: a crossing-free straight-line drawing, which for finite simple graphs is
equivalent to planarity by Fáry's theorem, as in the other planar restrictions under
`WantedExt/Complexity/NPComplete`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DISJOINT CONNECTING PATHS for planar graphs is NP-complete.** Source: Garey and Johnson
(1979), [ND40], comment; Lynch (1975). -/
public theorem_wanted disjointConnectingPathsPlanar_npComplete :
    disjointConnectingPathsPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L disjointConnectingPathsPlanarDec

end MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPathsPlanar
