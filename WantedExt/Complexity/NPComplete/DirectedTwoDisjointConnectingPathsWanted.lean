/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED DISJOINT CONNECTING PATHS with `k = 2` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND40] DISJOINT CONNECTING PATHS,
p. 217 (the problem; its comment records that the directed version is NP-complete in general);
S. Fortune, J. Hopcroft, and J. Wyllie, "The directed subgraph homeomorphism problem",
Theoretical Computer Science 10 (1980), 111-121, doi:10.1016/0304-3975(80)90009-2 (the
directed problem is NP-complete already for two pairs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPaths

/-!
# DIRECTED DISJOINT CONNECTING PATHS with `k = 2` is NP-complete

INSTANCE: a directed graph `G = (V, A)` and two disjoint vertex pairs `(s₁, t₁)`, `(s₂, t₂)`.
QUESTION: does `G` contain two vertex-disjoint directed paths, one from `s₁` to `t₁` and one
from `s₂` to `t₂`?

This is DISJOINT CONNECTING PATHS ([ND40]) for directed graphs, with the number of pairs fixed
at `k = 2`. The vertices are `0, ..., n - 1` and the arcs are a list of ordered pairs without
repetitions or loops, as in the sibling `DirectedDisjointPathsWanted.lean` (the directed
problem with any number of pairs). "Disjoint vertex pairs" means that the four vertices
`s₁, t₁, s₂, t₂` are pairwise distinct. A directed path from `s` to `t` is a list of pairwise
distinct vertices that starts at `s`, ends at `t`, and has an arc from each vertex to the next
(`List.IsChain`); two paths are vertex-disjoint when their vertex lists are disjoint.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DIRECTED DISJOINT CONNECTING PATHS with `k = 2` is NP-complete.** Source: Garey and
Johnson (1979), [ND40]; Fortune, Hopcroft, and Wyllie (1980). -/
public theorem_wanted directedTwoDisjointConnectingPaths_npComplete :
    directedTwoDisjointConnectingPathsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedTwoDisjointConnectingPathsDec

end MetaMathlibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPaths
