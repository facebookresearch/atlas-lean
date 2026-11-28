/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EFFICIENT EDGE DOMINATION is NP-complete

Source:
D. L. Grinstead, P. J. Slater, N. A. Sherwani and N. D. Holmes, "Efficient edge domination
problems in graphs", Information Processing Letters 48 (1993), 221-228,
doi:10.1016/0020-0190(93)90084-M.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EfficientEdgeDominationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EfficientEdgeDomination

/-!
# EFFICIENT EDGE DOMINATION is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected). QUESTION: is there an efficient
edge dominating set, i.e. a set `E' ⊆ E` such that every edge of `E` is dominated by exactly one
edge of `E'`, where an edge dominates itself and every edge sharing an endpoint with it? Such a
set is also called a dominating induced matching; equivalently, `E'` is an efficient dominating
set (perfect code) of the line graph `L(G)`.

Edges are the elements of `(Graph i).edgeSet`, and two distinct edges share an endpoint exactly
when they are adjacent in Mathlib's `SimpleGraph.lineGraph`; so "`d` dominates `e`" is
`d = e ∨ (Graph i).lineGraph.Adj d e`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EFFICIENT EDGE DOMINATION is NP-complete.** Source: Grinstead, Slater, Sherwani and
Holmes (1993). -/
public theorem_wanted efficientEdgeDomination_npComplete :
    efficientEdgeDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L efficientEdgeDominationDec

end MetaMathlibExt.Complexity.NPComplete.EfficientEdgeDomination
