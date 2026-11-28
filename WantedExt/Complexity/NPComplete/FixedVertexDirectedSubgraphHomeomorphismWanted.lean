/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM is NP-complete for every fixed pattern whose arcs
share neither a common tail nor a common head

Source:
S. Fortune, J. Hopcroft and J. Wyllie, "The directed subgraph homeomorphism problem",
Theoretical Computer Science 10 (1980), 111-121, doi:10.1016/0304-3975(80)90009-2;
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 2 (1981), 393-405,
doi:10.1016/0196-6774(81)90037-7, entry [2] SUBGRAPH HOMEOMORPHISM (FOR A FIXED GRAPH H).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FixedVertexDirectedSubgraphHomeomorphismDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedVertexDirectedSubgraphHomeomorphism

open MetaMathlibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPaths (IsDirectedPath)

/-!
# FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM is NP-complete

Fix a directed pattern graph `H = (V_H, A_H)` with vertices `0, ..., k - 1` and arc list `A_H`
(no repeated arcs, no loops).

INSTANCE: a directed graph `G = (V, A)` and an injective map `m : V_H → V` prescribing the image of
each pattern vertex.
QUESTION: does `G` contain a subgraph homeomorphic to `H` with the prescribed branch vertices,
i.e., for each arc `(u, v)` of `H` a directed path in `G` from `m u` to `m v`, such that no path
passes through a prescribed vertex `m w` other than its two ends, and two different paths share
no vertex other than prescribed ones (the paths are internally vertex-disjoint)?

Johnson's column records the classification of Fortune, Hopcroft and Wyllie: the problem is
polynomial-time solvable if all arcs of `H` share a common tail, or all share a common head; for
all other fixed `H` it is NP-complete. The theorem below states the NP-complete half for every
fixed pattern without repeated arcs or loops: one decision problem per pattern `(k, A_H)`, and
the hypotheses say that no `r` is the tail of every arc and no `r` is the head of every arc (with
`r : ℕ`, so the empty pattern counts as a star and is excluded). The case where `H` is two
disjoint arcs is `DirectedTwoDisjointConnectingPathsWanted`, whose directed-path predicate
`IsDirectedPath` (distinct vertices, first `s`, last `t`, an arc from each vertex to the next) is
reused here.

The vertices of `G` are `0, ..., n - 1`, its arcs a list of ordered pairs without repetitions or
loops (as in `DirectedTwoDisjointConnectingPathsWanted`), and `m` is the list
`[m 0, ..., m (k - 1)]` of pairwise distinct vertices. Path `j` realizes the `j`-th arc of `A_H`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM is NP-complete** for every fixed pattern
without repeated arcs or loops in which no vertex is the tail of every arc and no vertex is the
head of every arc. Source: Fortune, Hopcroft and Wyllie (1980); Johnson (1981). -/
public theorem_wanted fixedVertexDirectedSubgraphHomeomorphism_npComplete
    (k : ℕ) (AH : List (ℕ × ℕ)) (hH : PatternWellFormed k AH)
    (htail : ¬ ∃ r : ℕ, ∀ a ∈ AH, a.1 = r) (hhead : ¬ ∃ r : ℕ, ∀ a ∈ AH, a.2 = r) :
    fixedVertexDirectedSubgraphHomeomorphismDec k AH ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (fixedVertexDirectedSubgraphHomeomorphismDec k AH)

end MetaMathlibExt.Complexity.NPComplete.FixedVertexDirectedSubgraphHomeomorphism
