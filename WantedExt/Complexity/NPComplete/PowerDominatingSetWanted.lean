/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POWER DOMINATING SET is NP-complete

Source:
T. W. Haynes, S. M. Hedetniemi, S. T. Hedetniemi, and M. A. Henning, "Domination in graphs
applied to electric power networks", SIAM Journal on Discrete Mathematics 15(4) (2002), 519-529,
doi:10.1137/S0895480100375831;
D. J. Brueni and L. S. Heath, "The PMU placement problem", SIAM Journal on Discrete Mathematics
19(3) (2005), 744-761, doi:10.1137/S0895480103432556 (vertex form of the observation rules).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PowerDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PowerDominatingSet

/-!
# POWER DOMINATING SET is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) and a positive integer `K`.
QUESTION: is there a set `S ⊆ V` with `|S| ≤ K` that observes all of `V` under the rules:
the closed neighborhood `N[S]` is observed; an observed vertex with exactly one unobserved
neighbor makes that neighbor observed?

The observed set is the least set of vertices closed under the two rules (`Observed`, an
inductive predicate): every vertex of `S` and every neighbor of a vertex of `S` is observed, and
if `v` is observed, `u` is a neighbor of `v` and every other neighbor of `v` is observed, then
`u` is observed. This is the result of applying the propagation rule until nothing changes; the
order of the applications does not matter, because a vertex that may propagate keeps that
ability until its last unobserved neighbor is observed. As in the source, `K` is positive.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **POWER DOMINATING SET is NP-complete.** Source: Haynes, Hedetniemi, Hedetniemi, and
Henning (2002). -/
public theorem_wanted powerDominatingSet_npComplete :
    powerDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L powerDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.PowerDominatingSet
