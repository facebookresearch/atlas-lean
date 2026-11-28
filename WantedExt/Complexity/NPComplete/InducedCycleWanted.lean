/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED CYCLE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT23] INDUCED PATH, comment ("The
same result holds for the variant in which 'simple path' is replaced by 'simple cycle'"),
attributed to M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of the
10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InducedCycleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedCycle

open MetaMathlibExt.Complexity.NPComplete.InducedPath (InducedPathInstance)

/-!
# INDUCED CYCLE is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a subset `V' ⊆ V` with `|V'| ≥ K` such that the subgraph induced by `V'` is a
simple cycle on `|V'|` vertices?

This is the variant of INDUCED PATH (Garey and Johnson [GT23], `InducedPathWanted`) in which
"simple path" is replaced by "simple cycle"; the comment to [GT23] states that "the same result
holds", with the reference [Yannakakis, 1978c]. The instance type, the graph and the
well-formedness (a simple edge list and `0 < K ≤ |V|`) are those of `InducedPathWanted`.

"The subgraph induced by `V'` is a simple cycle on `|V'|` vertices" is Mathlib's induced
containment `(SimpleGraph.cycleGraph m).IsIndContained G` with `m = |V'|`, as `InducedPathWanted`
uses `SimpleGraph.pathGraph`: an embedding `cycleGraph m ↪g G` is injective and preserves and
reflects adjacency, so its range has `m` vertices and induces a copy of `cycleGraph m`. A simple
cycle has at least three vertices, and `cycleGraph m` is a cycle exactly when `m ≥ 3`
(`cycleGraph 2` is a single edge), so the question also asks for `m ≥ 3`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDUCED CYCLE is NP-complete.** Source: Garey and Johnson (1979), [GT23];
Yannakakis (1978). -/
public theorem_wanted inducedCycle_npComplete :
    inducedCycleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inducedCycleDec

end MetaMathlibExt.Complexity.NPComplete.InducedCycle
