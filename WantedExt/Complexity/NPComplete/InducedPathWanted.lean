/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT23] INDUCED PATH;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 4, the connected node-deletion problem, for
the property "is a path").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InducedPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedPath

/-!
# INDUCED PATH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is there a subset
`V' ⊆ V` with `|V'| ≥ K` such that the subgraph induced by `V'` is a simple path on `|V'|`
vertices?

"The subgraph induced by `V'` is a simple path on `|V'|` vertices" is Mathlib's induced
containment `(SimpleGraph.pathGraph m).IsIndContained G` with `m = |V'|`: an embedding
`pathGraph m ↪g G` is injective and both preserves and reflects adjacency, so its range `V'` has
`m` vertices and induces a copy of the path graph on `m` vertices
(`SimpleGraph.isIndContained_iff_exists_iso_induce`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDUCED PATH is NP-complete.** Source: Garey and Johnson (1979), [GT23];
Yannakakis (1978), Theorem 4. -/
public theorem_wanted inducedPath_npComplete :
    inducedPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inducedPathDec

end MetaMathlibExt.Complexity.NPComplete.InducedPath
