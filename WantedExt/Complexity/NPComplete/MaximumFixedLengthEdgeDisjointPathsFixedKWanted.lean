/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM FIXED-LENGTH EDGE-DISJOINT PATHS with fixed `K ≥ 4` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND42] MAXIMUM FIXED-LENGTH DISJOINT PATHS,
p. 218, comment ("Corresponding problem for edge-disjoint paths is NP-complete for fixed
K ≥ 4");
A. Itai, Y. Perl and Y. Shiloach, "The complexity of finding maximum disjoint paths with length
constraints", Networks 12(3) (1982), 277-286, doi:10.1002/net.3230120306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumFixedLengthEdgeDisjointPathsFixedKDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthEdgeDisjointPathsFixedK

open MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPaths
open MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted

/-!
# MAXIMUM FIXED-LENGTH EDGE-DISJOINT PATHS with fixed `K ≥ 4` is NP-complete

For a fixed constant `K ≥ 4`: given a graph `G = (V, E)`, specified vertices `s` and `t`, and a
positive integer `J ≤ |V|`, does `G` contain `J` or more mutually edge-disjoint paths from `s` to
`t`, each involving exactly `K` edges?

This is the edge-disjoint version of MAXIMUM FIXED-LENGTH DISJOINT PATHS
(`WantedExt.Complexity.NPComplete.MaximumFixedLengthDisjointPathsWanted`), with `K` no longer
part of the instance. The instance is the graph, `s`, `t` and `J`, and `withLength i K` appends
the fixed `K` to obtain an instance of that problem, whose `Graph` and `WellFormed` (simple edge
list, `s ≠ t`, `0 < J ≤ |V|`, `0 < K ≤ |V|`) are reused unchanged. Only the question changes:
mutual edge-disjointness is `IsEdgeDisjointSTPaths` from
`MathlibExt.Combinatorics.SimpleGraph.MengerEdge` (two distinct paths of the family share no
edge). Since `s ≠ t`, every path from `s` to `t` has an edge, so an edge-disjoint family of `J`
paths consists of `J` different paths, and "`J` or more" paths is the same as `J` paths.
"Involving exactly `K` edges" is `Walk.length = K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM FIXED-LENGTH EDGE-DISJOINT PATHS is NP-complete for every fixed `K ≥ 4`.**
Source: Garey and Johnson (1979), [ND42], comment; Itai, Perl and Shiloach (1982). -/
public theorem_wanted maximumFixedLengthEdgeDisjointPathsFixedK_npComplete (K : ℕ)
    (hK : 4 ≤ K) :
    fixedLengthDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (fixedLengthDec K)

end MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthEdgeDisjointPathsFixedK
