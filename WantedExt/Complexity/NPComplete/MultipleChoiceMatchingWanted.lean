/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE CHOICE MATCHING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT55] MULTIPLE CHOICE MATCHING;
A. Itai, M. Rodeh and S. L. Tanimoto, "Some matching problems for bipartite graphs",
Journal of the ACM 25 (1978), 517-525, doi:10.1145/322092.322093;
A. Itai and M. Rodeh, "Some matching problems", Automata, Languages and Programming (ICALP
1977), Lecture Notes in Computer Science 52, Springer (1977), 258-268,
doi:10.1007/3-540-08342-1_20.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipleChoiceMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleChoiceMatching

/-!
# MULTIPLE CHOICE MATCHING is NP-complete

Given a graph `G = (V, E)`, a partition of `E` into disjoint sets `E₁, E₂, ..., E_J`, and a
positive integer `K`, is there a subset `E' ⊆ E` with `|E'| ≥ K` such that no two edges in
`E'` share a common vertex and such that `E'` contains at most one edge from each `Eᵢ`?

The vertices are `0, ..., n - 1`. Each edge is listed once, as a triple `(u, v, c)` saying
that the edge `{u, v}` lies in the class `E_c`; the classes are the sets of edges sharing a
label, so the labels give a partition of `E` into disjoint sets. The subset `E'` is the edge
set of a subgraph `M` of `G` that is a matching (`SimpleGraph.Subgraph.IsMatching`), which
holds exactly when no two of its edges share a vertex.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPLE CHOICE MATCHING is NP-complete.** Source: Garey and Johnson (1979), [GT55];
Itai, Rodeh and Tanimoto (1978); Itai and Rodeh (1977). -/
public theorem_wanted multipleChoiceMatching_npComplete :
    multipleChoiceMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleChoiceMatchingDec

end MetaMathlibExt.Complexity.NPComplete.MultipleChoiceMatching
