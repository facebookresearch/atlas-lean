/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BALANCED BICLIQUE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BALANCED COMPLETE
BIPARTITE SUBGRAPH; D. S. Johnson, "The NP-completeness column" (1987).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BalancedBicliqueDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BalancedBiclique

/-!
# BALANCED BICLIQUE is NP-complete

An undirected graph and a bound `K`. The question is whether the graph contains a complete
bipartite subgraph `K_{K,K}`: two disjoint sets of `K` vertices each, with every cross pair
adjacent. No inducedness is required.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BALANCED BICLIQUE is NP-complete.** The decision problem BALANCED BICLIQUE belongs to NP,
and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), BALANCED COMPLETE BIPARTITE SUBGRAPH; D. S. Johnson, "The NP-
completeness column" (1987). -/
public theorem_wanted balancedBiclique_npComplete :
    balancedBicliqueDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L balancedBicliqueDec

end MetaMathlibExt.Complexity.NPComplete.BalancedBiclique
