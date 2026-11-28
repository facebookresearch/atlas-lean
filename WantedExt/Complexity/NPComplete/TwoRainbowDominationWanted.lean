/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-RAINBOW DOMINATION is NP-complete

Source:
B. Brešar and T. Kraner Šumenjak, "On the 2-rainbow domination in graphs", Discrete Applied
Mathematics 155(17) (2007), 2394-2400, doi:10.1016/j.dam.2007.07.018.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoRainbowDominationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoRainbowDomination

/-!
# 2-RAINBOW DOMINATION is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` and a non-negative integer `K`.
QUESTION: is there a 2-rainbow dominating function of weight at most `K`, that is, a function
`f : V → 𝒫({1, 2})` such that every vertex `v` with `f(v) = ∅` has neighbors whose labels
together cover `{1, 2}`, and `∑_{v ∈ V} |f(v)| ≤ K`?

Brešar and Kraner Šumenjak (2007) prove that deciding whether a graph has a 2-rainbow
dominating function of a given weight is NP-complete, even for bipartite or chordal graphs.

The two colors are `Fin 2`, vertices are `Fin n`, and the graph is
`Cslib.Complexity.Karp.edgeGraph n E`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **2-RAINBOW DOMINATION is NP-complete.** Source: Brešar and Kraner Šumenjak (2007). -/
public theorem_wanted twoRainbowDomination_npComplete :
    twoRainbowDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoRainbowDominationDec

end MetaMathlibExt.Complexity.NPComplete.TwoRainbowDomination
