/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PAIRED DOMINATION is NP-complete

Source:
T. W. Haynes and P. J. Slater, "Paired-domination in graphs", Networks 32(3) (1998), 199-206,
doi:10.1002/(SICI)1097-0037(199810)32:3<199::AID-NET4>3.0.CO;2-F.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PairedDominationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PairedDomination

/-!
# PAIRED DOMINATION is NP-complete

INSTANCE: a graph `G = (V, E)` without isolated vertices and a positive even integer `K`.
QUESTION: is there a paired-dominating set `V' ⊆ V` with `|V'| ≤ K`, that is, a dominating set
of `G` whose induced subgraph `G[V']` has a perfect matching?

The threshold is even as in Haynes and Slater's decision problem ("`γp(G) ≤ c`", `c` a positive
even integer); a paired-dominating set has even size, so an odd bound would be equivalent to the
next smaller even one. The graph is simple and given by an edge list on `Fin n`. Domination is MathlibExt's
`SimpleGraph.IsDominating`. A perfect matching of `G[V']` is a matching of `G` (Mathlib's
`SimpleGraph.Subgraph.IsMatching`) whose vertex set is exactly `V'`: its edges are edges of `G`
between vertices of `V'`, and every vertex of `V'` lies on exactly one of them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PAIRED DOMINATION is NP-complete.** Source: Haynes and Slater (1998). -/
public theorem_wanted pairedDomination_npComplete :
    pairedDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pairedDominationDec

end MetaMathlibExt.Complexity.NPComplete.PairedDomination
