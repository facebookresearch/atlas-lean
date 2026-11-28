/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE RANKING is NP-complete

Source:
T. W. Lam and F. L. Yue, "Edge ranking of graphs is hard", Discrete Applied Mathematics 85(1)
(1998), 71-86, doi:10.1016/S0166-218X(98)00029-8 (computing an optimal edge ranking of a
general graph is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EdgeRankingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeRanking

/-!
# EDGE RANKING is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have an edge ranking with at most `K` ranks, that is, a labeling
`f : E → {1, …, K}` of the edges such that every path between two distinct edges with the
same label `i` contains an edge with a label larger than `i`?

A path between two edges `e₁` and `e₂` is a path in `G` (a Mathlib `SimpleGraph.Walk` with
`IsPath`) whose first edge is `e₁` and whose last edge is `e₂`. Its other edges are the
intermediate edges, and since `e₁` and `e₂` carry the label `i`, an edge of the path with a
larger label is intermediate. Edges are elements of `Sym2 (Fin n)`; the labeling is a function
on `Sym2 (Fin n)` whose values on non-edges are irrelevant. `K` uses the canonical binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EDGE RANKING is NP-complete.** Source: Lam and Yue (1998). -/
public theorem_wanted edgeRanking_npComplete :
    edgeRankingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeRankingDec

end MetaMathlibExt.Complexity.NPComplete.EdgeRanking
