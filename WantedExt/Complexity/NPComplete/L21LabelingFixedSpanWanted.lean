/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# L(2,1)-LABELING WITH FIXED SPAN is NP-complete for every fixed span K ≥ 4

Source:
J. Fiala, T. Kloks and J. Kratochvíl, "Fixed-parameter complexity of λ-labelings", Discrete
Applied Mathematics 113 (2001), 59-72, doi:10.1016/S0166-218X(00)00387-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.L21LabelingFixedSpanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.L21LabelingFixedSpan

/-!
# L(2,1)-LABELING WITH FIXED SPAN is NP-complete for every fixed span K ≥ 4

A `λ`-labeling (an `L(2,1)`-labeling with span at most `λ`) of a graph is an assignment of
labels from `{0, …, λ}` to the vertices such that vertices at distance at most two get different
labels and adjacent vertices get labels at least two apart (Fiala, Kloks and Kratochvíl 2001).
For a fixed integer `K ≥ 4`: INSTANCE: a graph `G = (V, E)`. QUESTION: does `G` have a
`K`-labeling? Fiala, Kloks and Kratochvíl prove this NP-complete for every fixed `K ≥ 4`.

`K` is not part of the instance: it is a parameter of the decision problem
`l21LabelingFixedSpanDec K`, and the theorem is stated for every `K ≥ 4`. A labeling is a map
`f : Fin n → Fin (K + 1)`; adjacent vertices `u, v` satisfy `f u + 2 ≤ f v` or `f v + 2 ≤ f u`,
and two distinct vertices with a common neighbour (distance two) get different labels.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **L(2,1)-LABELING WITH FIXED SPAN `K` is NP-complete for every fixed `K ≥ 4`.** Source:
Fiala, Kloks and Kratochvíl (2001). -/
public theorem_wanted l21LabelingFixedSpan_npComplete (K : ℕ) (_hK : 4 ≤ K) :
    l21LabelingFixedSpanDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (l21LabelingFixedSpanDec K)

end MetaMathlibExt.Complexity.NPComplete.L21LabelingFixedSpan
